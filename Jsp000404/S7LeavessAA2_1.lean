import Jsp000404.S7Defs

namespace R2N4


set_option maxHeartbeats 5036000 in
theorem n7l_sAA2_H_I_H_I_L_0 (m : N7Model)
    (h0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (h1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  obtain ⟨_, h0emin, _⟩ := h0
  obtain ⟨h1bigk, _, _⟩ := h1
  obtain ⟨h2elo, _, _⟩ := h2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h12, h14, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h12, h13, h14, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h1, h13, h17, h4, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases h0emin with h19 | h19 | h19 | h19 | h19
                                · rcases h1bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h11, h12, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h11, h12, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h0, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h11, h12, h13, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h0, h11, h12, h13, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h1, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h6, hlam, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h11, h12, h13, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h1, h4, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h2, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h7, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h9, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h2, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p20_1]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h3, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h8, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h10, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [h11, hlam, p20_0]
                                  · obtain ⟨p20_0, p20_1, p20_2, p20_3⟩ := h20c
                                    linarith only [hlam, p20_0]
                                · linarith only [h19, hlam, ht01, ht12, u2elo0]
                                · linarith only [h19, h4, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h12, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h12, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h11, h12, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h11, h12, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h0, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h10, h11, h12, h13, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p48_1, u2elo0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h0, h11, h12, h13, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p48_1, u2elo0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h1, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h6, hlam, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h1, h12, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h1, h11, h12, h13, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p48_1, u2elo0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h2, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h7, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h9, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h11, h12, h13, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p48_1]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h3, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h8, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h10, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [h11, hlam, p48_0]
                                  · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                    linarith only [hlam, p48_0]
                                · linarith only [h19, h5, hlam, ht01, ht12, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                              · rcases h0emin with h77 | h77 | h77 | h77 | h77
                                · rcases h1bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h12, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h7, h75, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    rcases p78_3 (m.d 0 1) (by simp) with h83 | h83
                                    · rcases p78_3 (m.d 1 2) (by simp) with h84 | h84
                                      · linarith only [h0, h84, hlam]
                                      · linarith only [h8, h84, hlam]
                                    · linarith only [h83, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h0, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h12, h9, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h0, h12, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p78_1, u2elo0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h0, h75, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p78_1, u2elo0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h1, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h6, hlam, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h12, h9, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h1, h4, h75, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p78_1, u2elo0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h2, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h7, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h9, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h2, h75, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h3, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h8, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h10, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [h11, hlam, p78_0]
                                  · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                    linarith only [hlam, p78_0]
                                · linarith only [h77, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h77, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h7, h75, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h7, h75, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    rcases p110_3 (m.d 0 1) (by simp) with h115 | h115
                                    · rcases p110_3 (m.d 1 2) (by simp) with h116 | h116
                                      · linarith only [h0, h116, hlam]
                                      · linarith only [h116, h8, hlam]
                                    · linarith only [h115, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h0, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h12, h9, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h0, h12, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h0, h75, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h1, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h6, hlam, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h12, h9, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h1, h4, h75, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h2, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h7, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h9, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h2, h75, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h3, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h8, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h10, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [h11, hlam, p110_0]
                                  · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                                    linarith only [hlam, p110_0]
                                · linarith only [h5, h77, hlam, ht01, ht12, u2elo0]
                              · linarith only [h12, h75, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                              · linarith only [h1, h142, h4, h75, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · linarith only [h1, h11, h12, h142, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                            · linarith only [h0, h11, h146, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                              · linarith only [h11, h145, h148, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases h0emin with h150 | h150 | h150 | h150 | h150
                                · rcases h1bigk with h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h145, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    rcases p151_3 (m.d 0 1) (by simp) with h155 | h155
                                    · rcases p151_3 (m.d 1 2) (by simp) with h156 | h156
                                      · linarith only [h0, h156, hlam]
                                      · linarith only [h156, h7, hlam]
                                    · linarith only [h155, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    rcases p151_3 (m.d 0 1) (by simp) with h160 | h160
                                    · rcases p151_3 (m.d 1 2) (by simp) with h161 | h161
                                      · linarith only [h0, h161, hlam]
                                      · linarith only [h161, h8, hlam]
                                    · linarith only [h160, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h0, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h0, h145, h6, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h0, h145, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p151_1, u2elo0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h0, h11, h145, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p151_1, u2elo0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h1, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h6, hlam, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h1, h145, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h1, h11, h145, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p151_1, u2elo0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h2, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h7, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h9, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h11, hlam, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h3, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h8, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h10, hlam, p151_0]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [h145, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p151_1]
                                  · obtain ⟨p151_0, p151_1, p151_2, p151_3⟩ := h151c
                                    linarith only [hlam, p151_0]
                                · linarith only [h150, hlam, ht01, ht12, u2elo0]
                                · linarith only [h150, h4, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h145, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h10, hc01, hc35, hlam, hphi, ht0b, ht5b, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    rcases p187_3 (m.d 0 1) (by simp) with h191 | h191
                                    · rcases p187_3 (m.d 1 2) (by simp) with h192 | h192
                                      · linarith only [h0, h192, hlam]
                                      · linarith only [h192, h7, hlam]
                                    · linarith only [h191, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    rcases p187_3 (m.d 0 1) (by simp) with h196 | h196
                                    · rcases p187_3 (m.d 1 2) (by simp) with h197 | h197
                                      · linarith only [h0, h197, hlam]
                                      · linarith only [h197, h8, hlam]
                                    · linarith only [h196, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h0, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h145, h6, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h0, h145, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p187_1, u2elo0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p187_1, u2elo0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h1, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h6, hlam, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h1, h145, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h1, h145, h146, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p187_1, u2elo0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h2, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h7, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h9, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h11, hlam, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h3, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h8, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h10, hlam, p187_0]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [h145, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                                  · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                                    linarith only [hlam, p187_0]
                                · linarith only [h150, h5, hlam, ht01, ht12, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h222 | h222
                            · linarith only [h11, h145, h222, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h224 | h224
                              · linarith only [h11, h224, h9, hlam]
                              · rcases h0emin with h226 | h226 | h226 | h226 | h226
                                · rcases h1bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h145, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h11, h145, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h0, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h10, h145, h224, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h0, h145, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p227_1, u2elo0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h0, h11, h145, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p227_1, u2elo0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h1, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h6, hlam, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h145, h9, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h1, h11, h145, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p227_1, u2elo0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h2, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h7, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h9, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h11, hlam, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h3, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h8, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h10, hlam, p227_0]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [h145, h9, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p227_1]
                                  · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                                    linarith only [hlam, p227_0]
                                · linarith only [h226, hlam, ht01, ht12, u2elo0]
                                · linarith only [h226, h4, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h145, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h145, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h10, h145, h224, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h0, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h10, h145, h224, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h0, h145, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p255_1, u2elo0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p255_1, u2elo0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h1, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h6, hlam, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h145, h9, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h1, h145, h222, h4, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p255_1, u2elo0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h2, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h7, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h9, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h11, hlam, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h3, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h8, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h10, hlam, p255_0]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [h145, h9, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p255_1]
                                  · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                    linarith only [hlam, p255_0]
                                · linarith only [h226, h5, hlam, ht01, ht12, u2elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h10, h282, h9, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                            · linarith only [h0, h282, h285, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                              · linarith only [h10, h282, h284, h287, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                              · rcases h0emin with h289 | h289 | h289 | h289 | h289
                                · rcases h1bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h284, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h284, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    rcases p290_3 (m.d 0 1) (by simp) with h294 | h294
                                    · rcases p290_3 (m.d 1 2) (by simp) with h295 | h295
                                      · linarith only [h0, h295, hlam]
                                      · linarith only [h295, h7, hlam]
                                    · linarith only [h294, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h10, h284, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h0, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h284, h6, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h0, h284, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p290_1, u2elo0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h0, h10, h284, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p290_1, u2elo0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h1, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h6, hlam, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h10, h284, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h10, hlam, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h2, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h7, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h9, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h282, hlam, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h3, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h8, hlam, p290_0]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [h10, h284, h287, h7, hc34, hc45, hlam, hphi, p290_1]
                                  · obtain ⟨p290_0, p290_1, p290_2, p290_3⟩ := h290c
                                    linarith only [hlam, p290_0]
                                · linarith only [h289, hlam, ht01, ht12, u2elo0]
                                · linarith only [h289, h4, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h284, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h284, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    rcases p322_3 (m.d 0 1) (by simp) with h326 | h326
                                    · rcases p322_3 (m.d 1 2) (by simp) with h327 | h327
                                      · linarith only [h0, h327, hlam]
                                      · linarith only [h327, h7, hlam]
                                    · linarith only [h326, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h10, h284, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h0, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h284, h6, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h0, h284, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p322_1, u2elo0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p322_1, u2elo0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h1, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h6, hlam, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h1, h284, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h10, hlam, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h2, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h7, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h9, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h282, hlam, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h3, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h8, hlam, p322_0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p322_1]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [h284, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p322_1, u2elo0]
                                  · obtain ⟨p322_0, p322_1, p322_2, p322_3⟩ := h322c
                                    linarith only [hlam, p322_0]
                                · linarith only [h289, h5, hlam, ht01, ht12, u2elo0]
                          · linarith only [h10, h284, h9, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                          · linarith only [h354, h356, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                              · rcases h0emin with h360 | h360 | h360 | h360 | h360
                                · rcases h1bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h354, h359, hc01, hc45, hlam, hphi, ht0b, ht5b, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h354, h359, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    rcases p361_3 (m.d 0 1) (by simp) with h366 | h366
                                    · rcases p361_3 (m.d 1 2) (by simp) with h367 | h367
                                      · linarith only [h0, h367, hlam]
                                      · linarith only [h367, h8, hlam]
                                    · linarith only [h366, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h0, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h354, h359, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h0, h354, h359, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p361_1, u2elo0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p361_1, u2elo0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h1, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h6, hlam, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h9, hlam, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h8, h9, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h2, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h7, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p361_1]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h0, h354, h359, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p361_1, u2elo0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h3, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h8, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h354, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [h355, hlam, p361_0]
                                  · obtain ⟨p361_0, p361_1, p361_2, p361_3⟩ := h361c
                                    linarith only [hlam, p361_0]
                                · linarith only [h360, hlam, ht01, ht12, u2elo0]
                                · linarith only [h360, h4, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h354, h359, hc01, hc45, hlam, hphi, ht0b, ht5b, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h358, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    rcases p393_3 (m.d 0 1) (by simp) with h398 | h398
                                    · rcases p393_3 (m.d 1 2) (by simp) with h399 | h399
                                      · linarith only [h0, h399, hlam]
                                      · linarith only [h399, h8, hlam]
                                    · linarith only [h398, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h0, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h354, h359, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h0, h354, h359, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p393_1, u2elo0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h0, h354, h359, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p393_1, u2elo0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h1, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h6, hlam, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h9, hlam, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h1, h354, h359, hc01, hc45, hlam, hphi, ht0b, ht5b, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h2, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h7, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h0, h354, h359, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p393_1, u2elo0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h3, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h8, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h354, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [h355, hlam, p393_0]
                                  · obtain ⟨p393_0, p393_1, p393_2, p393_3⟩ := h393c
                                    linarith only [hlam, p393_0]
                                · linarith only [h360, h5, hlam, ht01, ht12, u2elo0]
                              · linarith only [h0, h358, h359, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h425 | h425
                              · linarith only [h354, h356, h358, h425, h9, hc23, hc34, hlam, hphi]
                              · linarith only [h355, h425, h9, hlam]
                        · linarith only [h354, h355, h9, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                          · linarith only [h4, h430, h9, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                              · rcases h0emin with h434 | h434 | h434 | h434 | h434
                                · rcases h1bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    rcases p435_3 (m.d 0 1) (by simp) with h438 | h438
                                    · rcases p435_3 (m.d 1 2) (by simp) with h439 | h439
                                      · linarith only [h0, h439, hlam]
                                      · linarith only [h439, h6, hlam]
                                    · linarith only [h438, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h432, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    rcases p435_3 (m.d 0 1) (by simp) with h444 | h444
                                    · rcases p435_3 (m.d 1 2) (by simp) with h445 | h445
                                      · linarith only [h0, h445, hlam]
                                      · linarith only [h445, h8, hlam]
                                    · linarith only [h444, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h0, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p435_1, u2elo1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h0, h432, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p435_1, u2elo0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h0, h354, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p435_1, u2elo0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h1, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h6, hlam, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h9, hlam, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h354, hlam, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h2, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h7, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h0, h354, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p435_1, u2elo0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h3, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h8, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [h429, hlam, p435_0]
                                  · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                    linarith only [hlam, p435_0]
                                · linarith only [h434, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h434, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    rcases p471_3 (m.d 0 1) (by simp) with h474 | h474
                                    · rcases p471_3 (m.d 1 2) (by simp) with h475 | h475
                                      · linarith only [h0, h475, hlam]
                                      · linarith only [h475, h6, hlam]
                                    · linarith only [h474, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h432, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    rcases p471_3 (m.d 0 1) (by simp) with h480 | h480
                                    · rcases p471_3 (m.d 1 2) (by simp) with h481 | h481
                                      · linarith only [h0, h481, hlam]
                                      · linarith only [h481, h8, hlam]
                                    · linarith only [h480, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h0, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p471_1, u2elo1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h0, h432, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p471_1, u2elo0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p471_1, u2elo0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h1, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h6, hlam, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h9, hlam, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h354, hlam, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h2, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h7, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h0, h354, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p471_1, u2elo0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h3, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h8, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [h429, hlam, p471_0]
                                  · obtain ⟨p471_0, p471_1, p471_2, p471_3⟩ := h471c
                                    linarith only [hlam, p471_0]
                                · linarith only [h434, h5, hlam, ht01, ht12, u2elo0]
                              · linarith only [h429, h432, h433, h8, h9, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                              · rcases h0emin with h508 | h508 | h508 | h508 | h508
                                · rcases h1bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    rcases p509_3 (m.d 0 1) (by simp) with h512 | h512
                                    · rcases p509_3 (m.d 1 2) (by simp) with h513 | h513
                                      · linarith only [h0, h513, hlam]
                                      · linarith only [h513, h6, hlam]
                                    · linarith only [h512, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h429, h430, h432, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h429, h430, h432, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h0, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p509_1, u2elo1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h0, h429, h430, h432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p509_1, u2elo0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h0, h429, h430, h432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p509_1, u2elo0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h1, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h6, hlam, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h9, hlam, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h354, hlam, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h2, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h7, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h6, h9, hc23, hc34, hlam, hphi, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h0, h429, h430, h432, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p509_1, u2elo0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h3, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h8, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h354, h6, hc23, hc35, hlam, hphi, p509_1]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [h429, hlam, p509_0]
                                  · obtain ⟨p509_0, p509_1, p509_2, p509_3⟩ := h509c
                                    linarith only [hlam, p509_0]
                                · linarith only [h508, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h508, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    rcases p541_3 (m.d 0 1) (by simp) with h544 | h544
                                    · rcases p541_3 (m.d 1 2) (by simp) with h545 | h545
                                      · linarith only [h0, h545, hlam]
                                      · linarith only [h545, h6, hlam]
                                    · linarith only [h544, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h429, h430, h432, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h429, h430, h432, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h0, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p541_1, u2elo1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h0, h429, h430, h432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p541_1, u2elo0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p541_1, u2elo0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h1, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h6, hlam, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h9, hlam, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h354, hlam, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h2, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h7, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h0, h354, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p541_1, u2elo0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h3, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h8, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p541_1]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [h429, hlam, p541_0]
                                  · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                    linarith only [hlam, p541_0]
                                · linarith only [h5, h508, hlam, ht01, ht12, u2elo0]
                              · linarith only [h429, h507, h9, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h573 | h573
                          · linarith only [h573, h6, h9, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h575 | h575
                            · linarith only [h0, h429, h575, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h577 | h577
                              · rcases h0emin with h578 | h578 | h578 | h578 | h578
                                · rcases h1bigk with h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    rcases p579_3 (m.d 0 1) (by simp) with h582 | h582
                                    · rcases p579_3 (m.d 1 2) (by simp) with h583 | h583
                                      · linarith only [h0, h583, hlam]
                                      · linarith only [h583, h6, hlam]
                                    · linarith only [h582, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    rcases p579_3 (m.d 0 1) (by simp) with h587 | h587
                                    · rcases p579_3 (m.d 1 2) (by simp) with h588 | h588
                                      · linarith only [h0, h588, hlam]
                                      · linarith only [h588, h7, hlam]
                                    · linarith only [h587, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    rcases p579_3 (m.d 0 1) (by simp) with h592 | h592
                                    · rcases p579_3 (m.d 1 2) (by simp) with h593 | h593
                                      · linarith only [h0, h593, hlam]
                                      · linarith only [h593, h8, hlam]
                                    · linarith only [h592, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h0, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p579_1, u2elo1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p579_1, u2elo0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p579_1, u2elo0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h1, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h6, hlam, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h9, hlam, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h354, hlam, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h2, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h7, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h429, hlam, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h3, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h8, hlam, p579_0]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [h429, h577, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p579_1]
                                  · obtain ⟨p579_0, p579_1, p579_2, p579_3⟩ := h579c
                                    linarith only [hlam, p579_0]
                                · linarith only [h578, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h578, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    rcases p619_3 (m.d 0 1) (by simp) with h622 | h622
                                    · rcases p619_3 (m.d 1 2) (by simp) with h623 | h623
                                      · linarith only [h0, h623, hlam]
                                      · linarith only [h6, h623, hlam]
                                    · linarith only [h622, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    rcases p619_3 (m.d 0 1) (by simp) with h627 | h627
                                    · rcases p619_3 (m.d 1 2) (by simp) with h628 | h628
                                      · linarith only [h0, h628, hlam]
                                      · linarith only [h628, h7, hlam]
                                    · linarith only [h627, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    rcases p619_3 (m.d 0 1) (by simp) with h632 | h632
                                    · rcases p619_3 (m.d 1 2) (by simp) with h633 | h633
                                      · linarith only [h0, h633, hlam]
                                      · linarith only [h633, h8, hlam]
                                    · linarith only [h632, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h0, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p619_1, u2elo1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h0, h573, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p619_1, u2elo0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p619_1, u2elo0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h1, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h6, hlam, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h9, hlam, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h354, hlam, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h2, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h7, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h429, hlam, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h3, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h8, hlam, p619_0]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [h429, h577, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p619_1]
                                  · obtain ⟨p619_0, p619_1, p619_2, p619_3⟩ := h619c
                                    linarith only [hlam, p619_0]
                                · linarith only [h5, h578, hlam, ht01, ht12, u2elo0]
                              · rcases h0emin with h658 | h658 | h658 | h658 | h658
                                · rcases h1bigk with h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    rcases p659_3 (m.d 0 1) (by simp) with h662 | h662
                                    · rcases p659_3 (m.d 1 2) (by simp) with h663 | h663
                                      · linarith only [h0, h663, hlam]
                                      · linarith only [h6, h663, hlam]
                                    · linarith only [h662, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    rcases p659_3 (m.d 0 1) (by simp) with h667 | h667
                                    · rcases p659_3 (m.d 1 2) (by simp) with h668 | h668
                                      · linarith only [h0, h668, hlam]
                                      · linarith only [h668, h7, hlam]
                                    · linarith only [h667, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    rcases p659_3 (m.d 0 1) (by simp) with h672 | h672
                                    · rcases p659_3 (m.d 1 2) (by simp) with h673 | h673
                                      · linarith only [h0, h673, hlam]
                                      · linarith only [h673, h8, hlam]
                                    · linarith only [h672, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h0, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p659_1, u2elo1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h0, h573, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p659_1, u2elo0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p659_1, u2elo0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h1, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h6, hlam, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h9, hlam, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h354, hlam, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h2, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h7, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h429, hlam, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h3, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h8, hlam, p659_0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p659_1]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p659_1, u2elo0]
                                  · obtain ⟨p659_0, p659_1, p659_2, p659_3⟩ := h659c
                                    linarith only [hlam, p659_0]
                                · linarith only [h658, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h658, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    rcases p699_3 (m.d 0 1) (by simp) with h702 | h702
                                    · rcases p699_3 (m.d 1 2) (by simp) with h703 | h703
                                      · linarith only [h0, h703, hlam]
                                      · linarith only [h6, h703, hlam]
                                    · linarith only [h702, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    rcases p699_3 (m.d 0 1) (by simp) with h707 | h707
                                    · rcases p699_3 (m.d 1 2) (by simp) with h708 | h708
                                      · linarith only [h0, h708, hlam]
                                      · linarith only [h7, h708, hlam]
                                    · linarith only [h707, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    rcases p699_3 (m.d 0 1) (by simp) with h712 | h712
                                    · rcases p699_3 (m.d 1 2) (by simp) with h713 | h713
                                      · linarith only [h0, h713, hlam]
                                      · linarith only [h713, h8, hlam]
                                    · linarith only [h712, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h0, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p699_1, u2elo1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h0, h573, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p699_1, u2elo0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p699_1, u2elo0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h1, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h6, hlam, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h9, hlam, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h354, hlam, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h2, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h7, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h429, hlam, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h3, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h8, hlam, p699_0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p699_1]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p699_1, u2elo0]
                                  · obtain ⟨p699_0, p699_1, p699_2, p699_3⟩ := h699c
                                    linarith only [hlam, p699_0]
                                · linarith only [h5, h658, hlam, ht01, ht12, u2elo0]
                  · linarith only [h5, h8, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
                    · linarith only [h6, h7, h740, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h744 | h744
                          · linarith only [h6, h7, h740, h744, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                              · rcases h0emin with h748 | h748 | h748 | h748 | h748
                                · rcases h1bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h742, h747, hc01, hc45, hlam, hphi, ht0b, ht5b, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    rcases p749_3 (m.d 0 1) (by simp) with h754 | h754
                                    · rcases p749_3 (m.d 1 2) (by simp) with h755 | h755
                                      · linarith only [h0, h755, hlam]
                                      · linarith only [h739, h755, hlam]
                                    · linarith only [h754, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h0, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h742, h747, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h7, hlam, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p749_1, u2elo3]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h1, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h6, hlam, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h740, hlam, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h1, h739, hc01, hc25, hlam, hphi, ht0b, ht5b, p749_1]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h2, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h7, hc12, hlam, hphi, p749_1, u2elo3]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p749_1, u2elo3]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h7, h742, h747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p749_1, u2elo3]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h3, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h739, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h742, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [h743, hlam, p749_0]
                                  · obtain ⟨p749_0, p749_1, p749_2, p749_3⟩ := h749c
                                    linarith only [hlam, p749_0]
                                · linarith only [h748, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h748, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h742, h747, hc01, hc45, hlam, hphi, ht0b, ht5b, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    rcases p781_3 (m.d 0 1) (by simp) with h786 | h786
                                    · rcases p781_3 (m.d 1 2) (by simp) with h787 | h787
                                      · linarith only [h0, h787, hlam]
                                      · linarith only [h739, h787, hlam]
                                    · linarith only [h786, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h0, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h742, h747, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h7, hlam, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h7, h742, h747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p781_1, u2elo3]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h1, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h6, hlam, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h740, hlam, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h1, h742, h747, hc01, hc45, hlam, hphi, ht0b, ht5b, p781_1]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h2, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h7, hc12, hlam, hphi, p781_1, u2elo3]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p781_1, u2elo3]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h7, h742, h747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p781_1, u2elo3]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h3, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h739, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h742, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [h743, hlam, p781_0]
                                  · obtain ⟨p781_0, p781_1, p781_2, p781_3⟩ := h781c
                                    linarith only [hlam, p781_0]
                                · linarith only [h5, h748, hlam, ht01, ht12, u2elo0]
                              · linarith only [h5, h6, h7, h744, h746, h747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h6, h7, h746, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h7, h739, h743, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h815 | h815
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h816 | h816
                          · linarith only [h6, h7, h816, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h818 | h818
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h819 | h819
                              · rcases h0emin with h820 | h820 | h820 | h820 | h820
                                · rcases h1bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    rcases p821_3 (m.d 0 1) (by simp) with h824 | h824
                                    · rcases p821_3 (m.d 1 2) (by simp) with h825 | h825
                                      · linarith only [h0, h825, hlam]
                                      · linarith only [h6, h825, hlam]
                                    · linarith only [h824, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    rcases p821_3 (m.d 0 1) (by simp) with h830 | h830
                                    · rcases p821_3 (m.d 1 2) (by simp) with h831 | h831
                                      · linarith only [h0, h831, hlam]
                                      · linarith only [h739, h831, hlam]
                                    · linarith only [h830, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h0, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p821_1, u2elo3]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h7, hlam, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p821_1, u2elo3]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h1, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h6, hlam, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h740, hlam, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h742, hlam, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h2, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h739, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p821_1, u2elo3]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h6, h7, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p821_1, u2elo3]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h3, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h739, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p821_1]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [h815, hlam, p821_0]
                                  · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                    linarith only [hlam, p821_0]
                                · linarith only [h820, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h820, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    rcases p857_3 (m.d 0 1) (by simp) with h860 | h860
                                    · rcases p857_3 (m.d 1 2) (by simp) with h861 | h861
                                      · linarith only [h0, h861, hlam]
                                      · linarith only [h6, h861, hlam]
                                    · linarith only [h860, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    rcases p857_3 (m.d 0 1) (by simp) with h866 | h866
                                    · rcases p857_3 (m.d 1 2) (by simp) with h867 | h867
                                      · linarith only [h0, h867, hlam]
                                      · linarith only [h739, h867, hlam]
                                    · linarith only [h866, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h0, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p857_1, u2elo1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h7, hlam, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p857_1, u2elo3]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h1, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h6, hlam, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h740, hlam, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h742, hlam, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h2, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p857_1, u2elo3]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h6, h7, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p857_1, u2elo3]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h3, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h739, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p857_1]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [h815, hlam, p857_0]
                                  · obtain ⟨p857_0, p857_1, p857_2, p857_3⟩ := h857c
                                    linarith only [hlam, p857_0]
                                · linarith only [h5, h820, hlam, ht01, ht12, u2elo0]
                              · linarith only [h5, h6, h7, h816, h818, h819, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h6, h7, h818, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h7, h739, h815, hlam]
                  · linarith only [h5, h6, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h4, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
              · rcases m.htr 1 2 4 (by decide) (by decide) with h898 | h898
                · rcases m.htr 1 2 5 (by decide) (by decide) with h899 | h899
                  · linarith only [h5, h899, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h902 | h902
                      · linarith only [h897, h899, h902, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h904 | h904
                        · linarith only [h897, h899, h901, h904, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h906 | h906
                          · linarith only [h0, h5, h897, h906, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · linarith only [h1, h4, h5, h901, h906, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
                      · linarith only [h898, h899, h901, h909, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                        · linarith only [h898, h899, h911, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                          · linarith only [h4, h5, h901, h913, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h915 | h915
                            · linarith only [h0, h5, h898, h911, h915, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                              · linarith only [h4, h5, h915, h917, hc23, hc34, hlam, hphi]
                              · rcases h0emin with h919 | h919 | h919 | h919 | h919
                                · rcases h1bigk with h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h898, h913, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    rcases p920_3 (m.d 0 1) (by simp) with h923 | h923
                                    · rcases p920_3 (m.d 1 2) (by simp) with h924 | h924
                                      · linarith only [h0, h924, hlam]
                                      · linarith only [h897, h924, hlam]
                                    · linarith only [h923, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    rcases p920_3 (m.d 0 1) (by simp) with h928 | h928
                                    · rcases p920_3 (m.d 1 2) (by simp) with h929 | h929
                                      · linarith only [h0, h929, hlam]
                                      · linarith only [h898, h929, hlam]
                                    · linarith only [h928, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h898, h899, h913, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h0, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h0, h5, h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p920_1, u2elo4]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h0, h5, h897, h901, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p920_1, u2elo4]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h899, hlam, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h1, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h897, hlam, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h901, hlam, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h909, hlam, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h2, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h898, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h2, h897, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h911, hlam, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h3, hlam, p920_0]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p920_1]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h3, h5, h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p920_1, u2elo4]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p920_1, u2elo4]
                                  · obtain ⟨p920_0, p920_1, p920_2, p920_3⟩ := h920c
                                    linarith only [hlam, p920_0]
                                · linarith only [h919, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h919, hlam, ht01, ht12, u2elo0]
                                · rcases h1bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h898, h913, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    rcases p956_3 (m.d 0 1) (by simp) with h959 | h959
                                    · rcases p956_3 (m.d 1 2) (by simp) with h960 | h960
                                      · linarith only [h0, h960, hlam]
                                      · linarith only [h897, h960, hlam]
                                    · linarith only [h959, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    rcases p956_3 (m.d 0 1) (by simp) with h964 | h964
                                    · rcases p956_3 (m.d 1 2) (by simp) with h965 | h965
                                      · linarith only [h0, h965, hlam]
                                      · linarith only [h898, h965, hlam]
                                    · linarith only [h964, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h898, h899, h913, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h0, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p956_1, u2elo1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h0, h5, h898, h913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p956_1, u2elo4]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h899, hlam, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h1, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h897, hlam, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h901, hlam, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h909, hlam, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h2, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h898, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h2, h897, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h911, hlam, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h3, hlam, p956_0]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h898, h913, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p956_1]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h3, h5, h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p956_1, u2elo4]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p956_1, u2elo4]
                                  · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                    linarith only [hlam, p956_0]
                                · linarith only [h5, h919, hlam, ht01, ht12, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h991 | h991
                  · linarith only [h5, h898, h991, hc02, hlam, hphi, u2elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
                    · linarith only [h897, h898, h993, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h995 | h995
                      · linarith only [h897, h991, h995, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h998 | h998
                          · linarith only [h4, h5, h993, h998, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1000 | h1000
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1001 | h1001
                              · rcases h0emin with h1002 | h1002 | h1002 | h1002 | h1002
                                · rcases h1bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    rcases p1003_3 (m.d 0 1) (by simp) with h1006 | h1006
                                    · rcases p1003_3 (m.d 1 2) (by simp) with h1007 | h1007
                                      · linarith only [h0, h1007, hlam]
                                      · linarith only [h1007, h897, hlam]
                                    · linarith only [h1006, hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, h991, h997, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, h991, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h0, hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, h991, h995, hc23, hc35, hlam, hphi, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h898, hlam, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h991, hlam, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h1, hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, hlam, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h993, hlam, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h995, hlam, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h2, hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h898, hc12, hlam, hphi, p1003_1, u2elo3]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1003_1, u2elo3]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h898, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1003_1, u2elo3]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h3, hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h897, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h1000, h3, h5, h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1003_1, u2elo3]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [h997, hlam, p1003_0]
                                  · obtain ⟨p1003_0, p1003_1, p1003_2, p1003_3⟩ := h1003c
                                    linarith only [hlam, p1003_0]
                                · linarith only [h1000, h1002, h5, hlam, ht01, ht12, u2elo3]
                                · linarith only [h1000, h1002, h4, h5, hlam, ht01, ht12, u2elo3]
                                · rcases h1bigk with h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    rcases p1035_3 (m.d 0 1) (by simp) with h1038 | h1038
                                    · rcases p1035_3 (m.d 1 2) (by simp) with h1039 | h1039
                                      · linarith only [h0, h1039, hlam]
                                      · linarith only [h1039, h897, hlam]
                                    · linarith only [h1038, hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h997, hc01, hc45, hlam, hphi, ht0b, ht5b, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, h991, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h0, hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1035_1, u2elo1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h898, hlam, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h991, hlam, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h1, hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, hlam, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h993, hlam, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h995, hlam, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h2, hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1035_1, u2elo3]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, h898, h991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1035_1, u2elo3]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h3, hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h897, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1035_1]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h3, h5, h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1035_1, u2elo4]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [h997, hlam, p1035_0]
                                  · obtain ⟨p1035_0, p1035_1, p1035_2, p1035_3⟩ := h1035c
                                    linarith only [hlam, p1035_0]
                                · linarith only [h1002, h5, hlam, ht01, ht12, u2elo4]
                              · linarith only [h0, h1000, h1001, h5, h897, h998, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h1000, h897, h898, h997, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1068 | h1068
                          · linarith only [h0, h1068, h5, h897, h993, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1070 | h1070
                            · linarith only [h1070, h897, h898, h997, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · linarith only [h1070, h897, h898, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h4, h5, h897, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1074 | h1074
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1075 | h1075
              · linarith only [h1075, h4, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1077 | h1077
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1078 | h1078
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1079 | h1079
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1080 | h1080
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1081 | h1081
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1082 | h1082
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1083 | h1083
                            · linarith only [h0, h1077, h1083, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · linarith only [h0, h1077, h1081, h1082, h1083, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h0, h1077, h1079, h1081, h1082, h4, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1087 | h1087
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1088 | h1088
                            · linarith only [h0, h1077, h1081, h1088, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1090 | h1090
                              · linarith only [h0, h1077, h1080, h1081, h1087, h1090, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · rcases h0emin with h1092 | h1092 | h1092 | h1092 | h1092
                                · rcases h1bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1078, h1087, h1088, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1093_1]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1075, h1078, h1087, h1088, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1093_1]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    rcases p1093_3 (m.d 0 1) (by simp) with h1097 | h1097
                                    · rcases p1093_3 (m.d 1 2) (by simp) with h1098 | h1098
                                      · linarith only [h0, h1098, hlam]
                                      · linarith only [h1077, h1098, hlam]
                                    · linarith only [h1097, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    rcases p1093_3 (m.d 0 1) (by simp) with h1102 | h1102
                                    · rcases p1093_3 (m.d 1 2) (by simp) with h1103 | h1103
                                      · linarith only [h0, h1103, hlam]
                                      · linarith only [h1078, h1103, hlam]
                                    · linarith only [h1102, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h0, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1075, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h0, h1077, h1087, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1, u2elo2]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h0, h1077, h1081, h1087, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1, u2elo2]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1093_1]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1, h1077, h1087, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1, u2elo2]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1, h1077, h1081, h1087, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1, u2elo2]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h2, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1077, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1079, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1081, hlam, p1093_1]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h3, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1078, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1080, hlam, p1093_0]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [h1077, h1087, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1093_1]
                                  · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                    linarith only [hlam, p1093_0]
                                · linarith only [h1092, hlam, ht01, ht12, u2elo0]
                                · linarith only [h1092, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1078, h1087, h1088, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1129_1]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1075, h1078, h1087, h1088, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1129_1]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    rcases p1129_3 (m.d 0 1) (by simp) with h1133 | h1133
                                    · rcases p1129_3 (m.d 1 2) (by simp) with h1134 | h1134
                                      · linarith only [h0, h1134, hlam]
                                      · linarith only [h1077, h1134, hlam]
                                    · linarith only [h1133, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    rcases p1129_3 (m.d 0 1) (by simp) with h1138 | h1138
                                    · rcases p1129_3 (m.d 1 2) (by simp) with h1139 | h1139
                                      · linarith only [h0, h1139, hlam]
                                      · linarith only [h1078, h1139, hlam]
                                    · linarith only [h1138, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h0, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1075, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1077, h1087, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1129_1, u2elo1]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h0, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1129_1]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1, h1077, h1087, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1129_1, u2elo2]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1, h1078, h1087, h1088, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1129_1, u2elo2]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h2, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1077, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1079, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1081, hlam, p1129_1]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h3, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1078, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1080, hlam, p1129_0]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [h1077, h1087, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1129_1]
                                  · obtain ⟨p1129_0, p1129_1, p1129_2, p1129_3⟩ := h1129c
                                    linarith only [hlam, p1129_0]
                                · linarith only [h1074, h1092, hlam, ht01, ht12, u2elo0]
                          · linarith only [h1, h1079, h1087, h4, hlam]
                      · linarith only [h1075, h1078, h1080, hlam]
                    · linarith only [h1075, h1077, h1079, hlam]
                  · linarith only [h1074, h1077, h1078, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1168 | h1168
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1170 | h1170
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1171 | h1171
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1172 | h1172
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1173 | h1173
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1174 | h1174
                              · rcases h0emin with h1175 | h1175 | h1175 | h1175 | h1175
                                · rcases h1bigk with h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1168, h1173, hc01, hc45, hlam, hphi, ht0b, ht5b, p1176_1]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1169, h1174, hc01, hc45, hlam, hphi, ht0b, ht5b, p1176_1]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1077, h1168, h1173, hc01, hc45, hlam, hphi, ht0b, ht5b, p1176_1]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    rcases p1176_3 (m.d 0 1) (by simp) with h1181 | h1181
                                    · rcases p1176_3 (m.d 1 2) (by simp) with h1182 | h1182
                                      · linarith only [h0, h1182, hlam]
                                      · linarith only [h1168, h1182, hlam]
                                    · linarith only [h1181, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h0, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1075, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1077, hlam, p1176_1]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1077, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1176_1, u2elo3]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1176_1]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1, h1077, h1168, h1173, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1176_1, u2elo2]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1, h1168, h1173, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1176_1, u2elo2]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h2, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1168, h1173, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1176_1]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1169, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1, h1168, h1169, h1173, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1176_1, u2elo2]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h3, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1168, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1170, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [h1171, hlam, p1176_0]
                                  · obtain ⟨p1176_0, p1176_1, p1176_2, p1176_3⟩ := h1176c
                                    linarith only [hlam, p1176_0]
                                · linarith only [h1175, h4, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1175, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1168, h1173, hc01, hc45, hlam, hphi, ht0b, ht5b, p1208_1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1075, h1168, h1173, hc01, hc45, hlam, hphi, ht0b, ht5b, p1208_1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1077, h1168, h1173, hc01, hc45, hlam, hphi, ht0b, ht5b, p1208_1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    rcases p1208_3 (m.d 0 1) (by simp) with h1213 | h1213
                                    · rcases p1208_3 (m.d 1 2) (by simp) with h1214 | h1214
                                      · linarith only [h0, h1214, hlam]
                                      · linarith only [h1168, h1214, hlam]
                                    · linarith only [h1213, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h0, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1075, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1077, hlam, p1208_1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1168, h1173, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1208_1, u2elo1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1208_1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1, h1077, h1168, h1173, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1208_1, u2elo2]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1, h1168, h1173, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1208_1, u2elo2]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h2, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1168, h1173, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1208_1]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1169, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1, h1168, h1169, h1173, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1208_1, u2elo2]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h3, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1168, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1170, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [h1171, hlam, p1208_0]
                                  · obtain ⟨p1208_0, p1208_1, p1208_2, p1208_3⟩ := h1208c
                                    linarith only [hlam, p1208_0]
                                · linarith only [h1074, h1175, h4, hlam, ht01, ht12, u2elo2]
                              · linarith only [h0, h1168, h1173, h1174, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h1077, h1168, h1171, h1173, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h1169, h1172, h4, hlam]
                        · linarith only [h1077, h1168, h1171, hlam]
                      · linarith only [h1075, h1168, h1170, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1244 | h1244
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1245 | h1245
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1246 | h1246
                          · linarith only [h1075, h1169, h1246, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1248 | h1248
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1249 | h1249
                              · rcases h0emin with h1250 | h1250 | h1250 | h1250 | h1250
                                · rcases h1bigk with h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1168, h1248, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1075, h1168, h1248, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1075, h1168, h1169, h1248, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    rcases p1251_3 (m.d 0 1) (by simp) with h1256 | h1256
                                    · rcases p1251_3 (m.d 1 2) (by simp) with h1257 | h1257
                                      · linarith only [h0, h1257, hlam]
                                      · linarith only [h1168, h1257, hlam]
                                    · linarith only [h1256, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h0, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1075, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1077, hlam, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1251_1, u2elo0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1169, hlam, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1, h1168, h1246, h1248, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1251_1]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h2, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1077, hc12, hlam, hphi, p1251_1, u2elo3]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1077, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1251_1, u2elo3]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1077, h1168, h1248, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1251_1, u2elo3]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h3, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1168, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1244, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [h1245, hlam, p1251_0]
                                  · obtain ⟨p1251_0, p1251_1, p1251_2, p1251_3⟩ := h1251c
                                    linarith only [hlam, p1251_0]
                                · linarith only [h1246, h1250, h4, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h1246, h1250, h4, hc34, hlam, ht01, ht12, ht23]
                                · rcases h1bigk with h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1168, h1248, hc01, hc45, hlam, hphi, ht0b, ht5b, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1075, h1168, h1248, hc01, hc45, hlam, hphi, ht0b, ht5b, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1077, h1168, h1248, hc01, hc45, hlam, hphi, ht0b, ht5b, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    rcases p1283_3 (m.d 0 1) (by simp) with h1288 | h1288
                                    · rcases p1283_3 (m.d 1 2) (by simp) with h1289 | h1289
                                      · linarith only [h0, h1289, hlam]
                                      · linarith only [h1168, h1289, hlam]
                                    · linarith only [h1288, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h0, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1075, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1077, hlam, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1168, h1248, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1283_1, u2elo1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1169, hlam, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1, h1168, h1246, h1248, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1283_1]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h2, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1077, hc12, hlam, hphi, p1283_1, u2elo3]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1077, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1283_1, u2elo3]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1077, h1168, h1248, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1283_1, u2elo3]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h3, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1168, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1244, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [h1245, hlam, p1283_0]
                                  · obtain ⟨p1283_0, p1283_1, p1283_2, p1283_3⟩ := h1283c
                                    linarith only [hlam, p1283_0]
                                · linarith only [h1074, h1246, h1250, h4, hc34, hlam, ht01, ht12, ht23]
                              · linarith only [h1168, h1246, h1248, h1249, h4, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1074, h1077, h1245, h1248, h3, h4, hc12, hlam, hphi, u2elo2]
                        · linarith only [h1075, h1168, h1169, h1245, hlam]
                      · linarith only [h1075, h1168, h1244, hlam]
                  · linarith only [h1074, h1168, h4, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1319 | h1319
              · linarith only [h1319, h4, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1321 | h1321
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1322 | h1322
                  · linarith only [h0, h1074, h1322, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1324 | h1324
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1325 | h1325
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1326 | h1326
                        · linarith only [h1321, h1322, h1326, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1328 | h1328
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1329 | h1329
                            · linarith only [h0, h1321, h1326, h1329, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1331 | h1331
                              · linarith only [h1074, h1328, h1329, h1331, hc02, hlam, hphi, u2elo3]
                              · rcases h0emin with h1333 | h1333 | h1333 | h1333 | h1333
                                · rcases h1bigk with h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1321, h1328, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1321, h1322, h1325, h1328, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    rcases p1334_3 (m.d 0 1) (by simp) with h1338 | h1338
                                    · rcases p1334_3 (m.d 1 2) (by simp) with h1339 | h1339
                                      · linarith only [h0, h1339, hlam]
                                      · linarith only [h1321, h1339, hlam]
                                    · linarith only [h1338, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1321, h1322, h1328, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h0, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1319, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h0, h1321, h1328, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1334_1, u2elo2]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1322, hlam, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1, h1321, h1328, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1334_1, u2elo2]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1, h1321, h1322, h1328, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1334_1, u2elo2]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h2, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1321, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1324, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1326, hlam, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h3, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1321, h1328, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1334_1]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1325, hlam, p1334_0]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [h1074, h1321, h1328, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1334_1, u2elo4]
                                  · obtain ⟨p1334_0, p1334_1, p1334_2, p1334_3⟩ := h1334c
                                    linarith only [hlam, p1334_0]
                                · linarith only [h1333, hlam, ht01, ht12, u2elo0]
                                · linarith only [h1333, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1321, h1328, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1319, h1321, h1328, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    rcases p1366_3 (m.d 0 1) (by simp) with h1370 | h1370
                                    · rcases p1366_3 (m.d 1 2) (by simp) with h1371 | h1371
                                      · linarith only [h0, h1371, hlam]
                                      · linarith only [h1321, h1371, hlam]
                                    · linarith only [h1370, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1321, h1322, h1328, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h0, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1319, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1321, h1328, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1366_1, u2elo1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1322, hlam, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1, h1321, h1328, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1366_1, u2elo2]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1, h1322, h4, hc12, hlam, hphi, p1366_1, u2elo2]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h2, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1321, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1324, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1326, hlam, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h3, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1366_1]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1325, hlam, p1366_0]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [h1, h1321, h1325, h1328, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1366_1, u2elo2]
                                  · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                    linarith only [hlam, p1366_0]
                                · linarith only [h1074, h1333, hlam, ht01, ht12, u2elo4]
                          · linarith only [h1, h1324, h1328, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1398 | h1398
                        · linarith only [h1319, h1321, h1325, h1398, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1400 | h1400
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1401 | h1401
                            · linarith only [h1319, h1321, h1325, h1398, h1401, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1403 | h1403
                              · linarith only [h1074, h1400, h1401, h1403, hc02, hlam, hphi, u2elo3]
                              · rcases h0emin with h1405 | h1405 | h1405 | h1405 | h1405
                                · rcases h1bigk with h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c | h1406c
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1321, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1319, h1321, h1400, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    rcases p1406_3 (m.d 0 1) (by simp) with h1410 | h1410
                                    · rcases p1406_3 (m.d 1 2) (by simp) with h1411 | h1411
                                      · linarith only [h0, h1411, hlam]
                                      · linarith only [h1321, h1411, hlam]
                                    · linarith only [h1410, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1319, h1321, h1325, h1400, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h0, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1319, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h0, h1074, h1321, h1400, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1406_1, u2elo4]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1322, hlam, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1, h1321, h1400, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1406_1, u2elo2]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1325, hlam, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h2, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1321, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1324, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1398, hlam, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h3, hlam, p1406_0]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1321, h1400, h3, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1406_1]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1074, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1406_1, u2elo4]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [h1074, h1321, h1400, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1406_1, u2elo4]
                                  · obtain ⟨p1406_0, p1406_1, p1406_2, p1406_3⟩ := h1406c
                                    linarith only [hlam, p1406_0]
                                · linarith only [h1405, hlam, ht01, ht12, u2elo0]
                                · linarith only [h1405, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1321, h1400, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1319, h1321, h1400, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    rcases p1438_3 (m.d 0 1) (by simp) with h1442 | h1442
                                    · rcases p1438_3 (m.d 1 2) (by simp) with h1443 | h1443
                                      · linarith only [h0, h1443, hlam]
                                      · linarith only [h1321, h1443, hlam]
                                    · linarith only [h1442, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1321, h1322, h1400, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h0, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1319, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1321, h1400, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1438_1, u2elo1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1322, hlam, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1, h1321, h1400, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1438_1, u2elo2]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1325, hlam, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h2, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1321, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1324, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1398, hlam, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h3, hlam, p1438_0]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1438_1]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1074, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1438_1, u2elo4]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [h1074, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1438_1, u2elo4]
                                  · obtain ⟨p1438_0, p1438_1, p1438_2, p1438_3⟩ := h1438c
                                    linarith only [hlam, p1438_0]
                                · linarith only [h1074, h1405, hlam, ht01, ht12, u2elo4]
                          · linarith only [h0, h1, h1324, h1400, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1319, h1321, h1324, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1471 | h1471
                  · linarith only [h0, h1074, h1471, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1473 | h1473
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1474 | h1474
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1475 | h1475
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1476 | h1476
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1477 | h1477
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1478 | h1478
                              · rcases h0emin with h1479 | h1479 | h1479 | h1479 | h1479
                                · rcases h1bigk with h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    rcases p1480_3 (m.d 0 1) (by simp) with h1482 | h1482
                                    · rcases p1480_3 (m.d 1 2) (by simp) with h1483 | h1483
                                      · linarith only [h1483, hlam, p1480_0]
                                      · rcases p1480_3 (m.d 1 3) (by simp) with h1485 | h1485
                                        · linarith only [h1, h1485, hlam]
                                        · linarith only [h1319, h1485, hlam]
                                    · linarith only [h1482, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1473, h1478, hc01, hc45, hlam, hphi, ht0b, ht5b, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1473, h1478, hc01, hc45, hlam, hphi, ht0b, ht5b, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    rcases p1480_3 (m.d 0 1) (by simp) with h1491 | h1491
                                    · rcases p1480_3 (m.d 1 2) (by simp) with h1492 | h1492
                                      · linarith only [h0, h1492, hlam]
                                      · rcases p1480_3 (m.d 1 3) (by simp) with h1494 | h1494
                                        · linarith only [h1, h1494, hlam]
                                        · linarith only [h1474, h1494, hlam]
                                    · linarith only [h1491, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h0, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1319, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1321, hlam, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1471, hlam, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1, h1473, h1478, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1480_1, u2elo2]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1480_1, u2elo2]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h2, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1473, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1, h1471, h1473, h4, hc12, hlam, hphi, p1480_1, u2elo2]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h3, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1480_1]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1474, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [h1475, hlam, p1480_0]
                                  · obtain ⟨p1480_0, p1480_1, p1480_2, p1480_3⟩ := h1480c
                                    linarith only [hlam, p1480_0]
                                · linarith only [h1074, h1476, h1477, h1479, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1479, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    rcases p1520_3 (m.d 0 1) (by simp) with h1522 | h1522
                                    · rcases p1520_3 (m.d 1 2) (by simp) with h1523 | h1523
                                      · linarith only [h1523, hlam, p1520_0]
                                      · rcases p1520_3 (m.d 1 3) (by simp) with h1525 | h1525
                                        · linarith only [h1, h1525, hlam]
                                        · linarith only [h1319, h1525, hlam]
                                    · linarith only [h1522, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1473, h1478, hc01, hc45, hlam, hphi, ht0b, ht5b, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1473, h1478, hc01, hc45, hlam, hphi, ht0b, ht5b, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    rcases p1520_3 (m.d 0 1) (by simp) with h1531 | h1531
                                    · rcases p1520_3 (m.d 1 2) (by simp) with h1532 | h1532
                                      · linarith only [h0, h1532, hlam]
                                      · rcases p1520_3 (m.d 1 3) (by simp) with h1534 | h1534
                                        · linarith only [h1, h1534, hlam]
                                        · linarith only [h1474, h1534, hlam]
                                    · linarith only [h1531, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h0, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1319, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1321, hlam, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1471, hlam, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1, h1473, h1478, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1520_1, u2elo2]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1520_1, u2elo2]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h2, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1473, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1, h1471, h1473, h4, hc12, hlam, hphi, p1520_1, u2elo2]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h3, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1520_1]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1474, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [h1475, hlam, p1520_0]
                                  · obtain ⟨p1520_0, p1520_1, p1520_2, p1520_3⟩ := h1520c
                                    linarith only [hlam, p1520_0]
                                · linarith only [h1074, h1476, h1477, h1479, hlam, ht01, ht12, u2elo2]
                              · rcases h0emin with h1559 | h1559 | h1559 | h1559 | h1559
                                · rcases h1bigk with h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    rcases p1560_3 (m.d 0 1) (by simp) with h1562 | h1562
                                    · rcases p1560_3 (m.d 1 2) (by simp) with h1563 | h1563
                                      · linarith only [h1563, hlam, p1560_0]
                                      · rcases p1560_3 (m.d 1 3) (by simp) with h1565 | h1565
                                        · linarith only [h1, h1565, hlam]
                                        · linarith only [h1319, h1565, hlam]
                                    · linarith only [h1562, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1473, h1475, h1478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1560_1]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1475, h1478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1560_1]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1475, h1478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1560_1]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h0, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1319, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1321, hlam, p1560_1]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1471, hlam, p1560_1]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1, h4, hc12, hlam, hphi, p1560_1, u2elo2]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1, h1475, h1478, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1560_1, u2elo2]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1560_1, u2elo2]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h2, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1560_1]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1473, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1, h1471, h1473, h4, hc12, hlam, hphi, p1560_1, u2elo2]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h3, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1, h1473, h1475, h1478, h3, h4, hc01, hc12, hc34, hlam, hphi, ht0b, ht45, ht5b, p1560_1, u2elo2]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1474, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [h1475, hlam, p1560_0]
                                  · obtain ⟨p1560_0, p1560_1, p1560_2, p1560_3⟩ := h1560c
                                    linarith only [hlam, p1560_0]
                                · linarith only [h1074, h1476, h1477, h1559, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1559, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    rcases p1594_3 (m.d 0 1) (by simp) with h1596 | h1596
                                    · rcases p1594_3 (m.d 1 2) (by simp) with h1597 | h1597
                                      · linarith only [h1597, hlam, p1594_0]
                                      · rcases p1594_3 (m.d 1 3) (by simp) with h1599 | h1599
                                        · linarith only [h1, h1599, hlam]
                                        · linarith only [h1319, h1599, hlam]
                                    · linarith only [h1596, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1473, h1475, h1478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1594_1]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1475, h1478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1594_1]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1475, h1478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1594_1]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h0, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1319, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1321, hlam, p1594_1]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1471, hlam, p1594_1]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1, h4, hc12, hlam, hphi, p1594_1, u2elo2]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1, h1475, h1478, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1594_1, u2elo2]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1, u2elo2]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h2, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1594_1]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1473, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1, h1471, h1473, h4, hc12, hlam, hphi, p1594_1, u2elo2]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h3, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1, h1473, h1475, h1478, h3, h4, hc01, hc12, hc34, hlam, hphi, ht0b, ht45, ht5b, p1594_1, u2elo2]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1474, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [h1475, hlam, p1594_0]
                                  · obtain ⟨p1594_0, p1594_1, p1594_2, p1594_3⟩ := h1594c
                                    linarith only [hlam, p1594_0]
                                · linarith only [h1074, h1476, h1477, h1559, hlam, ht01, ht12, u2elo2]
                            · linarith only [h1, h1321, h1473, h1475, h1477, h4, hc12, hlam, hphi, u2elo2]
                          · linarith only [h1, h1473, h1476, h4, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1629 | h1629
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1630 | h1630
                            · linarith only [h1321, h1475, h1630, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1632 | h1632
                              · linarith only [h1473, h1475, h1632, hlam]
                              · rcases h0emin with h1634 | h1634 | h1634 | h1634 | h1634
                                · rcases h1bigk with h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    rcases p1635_3 (m.d 0 1) (by simp) with h1637 | h1637
                                    · rcases p1635_3 (m.d 1 2) (by simp) with h1638 | h1638
                                      · linarith only [h1638, hlam, p1635_0]
                                      · rcases p1635_3 (m.d 1 3) (by simp) with h1640 | h1640
                                        · linarith only [h1, h1640, hlam]
                                        · linarith only [h1319, h1640, hlam]
                                    · linarith only [h1637, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1473, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    rcases p1635_3 (m.d 0 1) (by simp) with h1645 | h1645
                                    · rcases p1635_3 (m.d 1 2) (by simp) with h1646 | h1646
                                      · linarith only [h0, h1646, hlam]
                                      · rcases p1635_3 (m.d 1 3) (by simp) with h1648 | h1648
                                        · linarith only [h1, h1648, hlam]
                                        · linarith only [h1473, h1648, hlam]
                                    · linarith only [h1645, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    rcases p1635_3 (m.d 0 1) (by simp) with h1652 | h1652
                                    · rcases p1635_3 (m.d 1 2) (by simp) with h1653 | h1653
                                      · linarith only [h0, h1653, hlam]
                                      · rcases p1635_3 (m.d 1 3) (by simp) with h1655 | h1655
                                        · linarith only [h1, h1655, hlam]
                                        · linarith only [h1474, h1655, hlam]
                                    · linarith only [h1652, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h0, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1319, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1321, hlam, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1471, hlam, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1635_1, u2elo2]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1635_1, u2elo2]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h2, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1473, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1475, hlam, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h3, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1635_1]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1474, hlam, p1635_0]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [h1074, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1635_1, u2elo4]
                                  · obtain ⟨p1635_0, p1635_1, p1635_2, p1635_3⟩ := h1635c
                                    linarith only [hlam, p1635_0]
                                · linarith only [h1074, h1634, hlam, ht01, ht12, u2elo4]
                                · linarith only [h1634, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    rcases p1681_3 (m.d 0 1) (by simp) with h1683 | h1683
                                    · rcases p1681_3 (m.d 1 2) (by simp) with h1684 | h1684
                                      · linarith only [h1684, hlam, p1681_0]
                                      · rcases p1681_3 (m.d 1 3) (by simp) with h1686 | h1686
                                        · linarith only [h1, h1686, hlam]
                                        · linarith only [h1319, h1686, hlam]
                                    · linarith only [h1683, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1473, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    rcases p1681_3 (m.d 0 1) (by simp) with h1691 | h1691
                                    · rcases p1681_3 (m.d 1 2) (by simp) with h1692 | h1692
                                      · linarith only [h0, h1692, hlam]
                                      · rcases p1681_3 (m.d 1 3) (by simp) with h1694 | h1694
                                        · linarith only [h1, h1694, hlam]
                                        · linarith only [h1473, h1694, hlam]
                                    · linarith only [h1691, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    rcases p1681_3 (m.d 0 1) (by simp) with h1698 | h1698
                                    · rcases p1681_3 (m.d 1 2) (by simp) with h1699 | h1699
                                      · linarith only [h0, h1699, hlam]
                                      · rcases p1681_3 (m.d 1 3) (by simp) with h1701 | h1701
                                        · linarith only [h1, h1701, hlam]
                                        · linarith only [h1474, h1701, hlam]
                                    · linarith only [h1698, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h0, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1319, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1321, hlam, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1471, hlam, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1681_1, u2elo2]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1681_1, u2elo2]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h2, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1473, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1475, hlam, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h3, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1681_1]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1474, hlam, p1681_0]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [h1, h1474, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1681_1, u2elo2]
                                  · obtain ⟨p1681_0, p1681_1, p1681_2, p1681_3⟩ := h1681c
                                    linarith only [hlam, p1681_0]
                                · linarith only [h1074, h1634, hlam, ht01, ht12, u2elo4]
                          · linarith only [h1, h1473, h1629, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1727 | h1727
                        · linarith only [h1473, h1474, h1727, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1729 | h1729
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1730 | h1730
                            · linarith only [h1321, h1727, h1730, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1732 | h1732
                              · linarith only [h1321, h1730, h1732, hc12, hc34, hlam, hphi, ht23]
                              · rcases h0emin with h1734 | h1734 | h1734 | h1734 | h1734
                                · rcases h1bigk with h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    rcases p1735_3 (m.d 0 1) (by simp) with h1737 | h1737
                                    · rcases p1735_3 (m.d 1 2) (by simp) with h1738 | h1738
                                      · linarith only [h1738, hlam, p1735_0]
                                      · rcases p1735_3 (m.d 1 3) (by simp) with h1740 | h1740
                                        · linarith only [h1, h1740, hlam]
                                        · linarith only [h1319, h1740, hlam]
                                    · linarith only [h1737, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1473, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    rcases p1735_3 (m.d 0 1) (by simp) with h1745 | h1745
                                    · rcases p1735_3 (m.d 1 2) (by simp) with h1746 | h1746
                                      · linarith only [h0, h1746, hlam]
                                      · rcases p1735_3 (m.d 1 3) (by simp) with h1748 | h1748
                                        · linarith only [h1, h1748, hlam]
                                        · linarith only [h1473, h1748, hlam]
                                    · linarith only [h1745, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1473, h1474, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h0, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1319, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1321, hlam, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1471, hlam, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1474, hc12, hc35, hlam, hphi, ht23, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1074, h1474, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1735_1, u2elo4]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1474, hlam, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h2, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1473, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1727, hlam, p1735_1]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h3, hlam, p1735_0]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1074, h3, hc12, hlam, hphi, p1735_1, u2elo4]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1074, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1735_1, u2elo4]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [h1074, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1735_1, u2elo4]
                                  · obtain ⟨p1735_0, p1735_1, p1735_2, p1735_3⟩ := h1735c
                                    linarith only [hlam, p1735_0]
                                · linarith only [h1734, h4, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1734, h4, hlam, ht01, ht12, u2elo2]
                                · rcases h1bigk with h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    rcases p1775_3 (m.d 0 1) (by simp) with h1777 | h1777
                                    · rcases p1775_3 (m.d 1 2) (by simp) with h1778 | h1778
                                      · linarith only [h1778, hlam, p1775_0]
                                      · rcases p1775_3 (m.d 1 3) (by simp) with h1780 | h1780
                                        · linarith only [h1, h1780, hlam]
                                        · linarith only [h1319, h1780, hlam]
                                    · linarith only [h1777, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1473, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    rcases p1775_3 (m.d 0 1) (by simp) with h1785 | h1785
                                    · rcases p1775_3 (m.d 1 2) (by simp) with h1786 | h1786
                                      · linarith only [h0, h1786, hlam]
                                      · rcases p1775_3 (m.d 1 3) (by simp) with h1788 | h1788
                                        · linarith only [h1, h1788, hlam]
                                        · linarith only [h1473, h1788, hlam]
                                    · linarith only [h1785, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1473, h1474, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h0, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1319, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1321, hlam, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1471, hlam, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1, h1321, h4, hc12, hlam, hphi, p1775_1, u2elo2]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1474, hlam, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h2, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1473, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1727, hlam, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h3, hlam, p1775_0]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1775_1]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1074, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1775_1, u2elo4]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [h1074, h1321, h3, hc12, hlam, hphi, p1775_1, u2elo4]
                                  · obtain ⟨p1775_0, p1775_1, p1775_2, p1775_3⟩ := h1775c
                                    linarith only [hlam, p1775_0]
                                · linarith only [h1074, h1734, hlam, ht01, ht12, u2elo4]
                          · linarith only [h0, h1, h1473, h1729, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1815 | h1815
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1816 | h1816
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1817 | h1817
                          · linarith only [h1473, h1815, h1817, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1819 | h1819
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1820 | h1820
                              · rcases h0emin with h1821 | h1821 | h1821 | h1821 | h1821
                                · rcases h1bigk with h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    rcases p1822_3 (m.d 0 1) (by simp) with h1824 | h1824
                                    · rcases p1822_3 (m.d 1 2) (by simp) with h1825 | h1825
                                      · linarith only [h1825, hlam, p1822_0]
                                      · rcases p1822_3 (m.d 1 3) (by simp) with h1827 | h1827
                                        · linarith only [h1, h1827, hlam]
                                        · linarith only [h1319, h1827, hlam]
                                    · linarith only [h1824, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1815, h1820, hc01, hc45, hlam, hphi, ht0b, ht5b, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1473, h1815, h1820, hc01, hc45, hlam, hphi, ht0b, ht5b, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    rcases p1822_3 (m.d 0 1) (by simp) with h1833 | h1833
                                    · rcases p1822_3 (m.d 1 2) (by simp) with h1834 | h1834
                                      · linarith only [h0, h1834, hlam]
                                      · rcases p1822_3 (m.d 1 3) (by simp) with h1836 | h1836
                                        · linarith only [h1, h1836, hlam]
                                        · linarith only [h1815, h1836, hlam]
                                    · linarith only [h1833, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h0, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1319, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1321, hlam, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1471, hlam, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1473, hlam, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1, h1817, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h2, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1321, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1822_1, u2elo3]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1321, h1471, hc12, hlam, hphi, p1822_1, u2elo3]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h3, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1822_1]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1815, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [h1816, hlam, p1822_0]
                                  · obtain ⟨p1822_0, p1822_1, p1822_2, p1822_3⟩ := h1822c
                                    linarith only [hlam, p1822_0]
                                · linarith only [h1817, h1821, h4, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h1817, h1821, h4, hc34, hlam, ht01, ht12, ht23]
                                · rcases h1bigk with h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    rcases p1862_3 (m.d 0 1) (by simp) with h1864 | h1864
                                    · rcases p1862_3 (m.d 1 2) (by simp) with h1865 | h1865
                                      · linarith only [h1865, hlam, p1862_0]
                                      · rcases p1862_3 (m.d 1 3) (by simp) with h1867 | h1867
                                        · linarith only [h1, h1867, hlam]
                                        · linarith only [h1319, h1867, hlam]
                                    · linarith only [h1864, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1815, h1820, hc01, hc45, hlam, hphi, ht0b, ht5b, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1473, h1815, h1820, hc01, hc45, hlam, hphi, ht0b, ht5b, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    rcases p1862_3 (m.d 0 1) (by simp) with h1873 | h1873
                                    · rcases p1862_3 (m.d 1 2) (by simp) with h1874 | h1874
                                      · linarith only [h0, h1874, hlam]
                                      · rcases p1862_3 (m.d 1 3) (by simp) with h1876 | h1876
                                        · linarith only [h1, h1876, hlam]
                                        · linarith only [h1815, h1876, hlam]
                                    · linarith only [h1873, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h0, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1319, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1321, hlam, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1471, hlam, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1473, hlam, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1, h1817, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h2, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1321, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1862_1, u2elo3]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1321, h1471, hc12, hlam, hphi, p1862_1, u2elo3]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h3, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1862_1]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1815, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [h1816, hlam, p1862_0]
                                  · obtain ⟨p1862_0, p1862_1, p1862_2, p1862_3⟩ := h1862c
                                    linarith only [hlam, p1862_0]
                                · linarith only [h1074, h1819, h1821, hlam, ht01, ht12, u2elo3]
                              · linarith only [h1817, h1820, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1321, h1816, h1819, hlam]
                        · linarith only [h1473, h1815, h1816, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                          · linarith only [h1319, h1473, h1905, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1907 | h1907
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1908 | h1908
                              · rcases h0emin with h1909 | h1909 | h1909 | h1909 | h1909
                                · rcases h1bigk with h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    rcases p1910_3 (m.d 0 1) (by simp) with h1912 | h1912
                                    · rcases p1910_3 (m.d 1 2) (by simp) with h1913 | h1913
                                      · linarith only [h1913, hlam, p1910_0]
                                      · rcases p1910_3 (m.d 1 3) (by simp) with h1915 | h1915
                                        · linarith only [h1, h1915, hlam]
                                        · linarith only [h1319, h1915, hlam]
                                    · linarith only [h1912, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    rcases p1910_3 (m.d 0 1) (by simp) with h1919 | h1919
                                    · rcases p1910_3 (m.d 1 2) (by simp) with h1920 | h1920
                                      · linarith only [h0, h1920, hlam]
                                      · rcases p1910_3 (m.d 1 3) (by simp) with h1922 | h1922
                                        · linarith only [h1922, hlam, p1910_0]
                                        · rcases p1910_3 (m.d 1 4) (by simp) with h1924 | h1924
                                          · linarith only [h1924, h2, hlam]
                                          · linarith only [h1473, h1924, hlam]
                                    · linarith only [h1919, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1904, hc01, hc45, hlam, hphi, ht0b, ht5b, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    rcases p1910_3 (m.d 0 1) (by simp) with h1929 | h1929
                                    · rcases p1910_3 (m.d 1 2) (by simp) with h1930 | h1930
                                      · linarith only [h0, h1930, hlam]
                                      · rcases p1910_3 (m.d 1 3) (by simp) with h1932 | h1932
                                        · linarith only [h1, h1932, hlam]
                                        · rcases p1910_3 (m.d 1 4) (by simp) with h1934 | h1934
                                          · linarith only [h1934, h2, hlam]
                                          · linarith only [h1904, h1934, hlam]
                                    · linarith only [h1929, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h0, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1319, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1321, hlam, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1471, hlam, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1815, hc12, hc35, hlam, hphi, ht23, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1473, hlam, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1815, hlam, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h2, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1321, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo3]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1321, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1910_1, u2elo3]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h3, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1910_1]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1074, h1319, h1907, h3, hc12, hlam, hphi, p1910_1, u2elo3]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [h1904, hlam, p1910_0]
                                  · obtain ⟨p1910_0, p1910_1, p1910_2, p1910_3⟩ := h1910c
                                    linarith only [hlam, p1910_0]
                                · linarith only [h1909, hlam, ht01, ht12, u2elo0]
                                · linarith only [h1905, h1909, h4, hc34, hlam, ht01, ht12, ht23]
                                · rcases h1bigk with h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c | h1960c
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    rcases p1960_3 (m.d 0 1) (by simp) with h1962 | h1962
                                    · rcases p1960_3 (m.d 1 2) (by simp) with h1963 | h1963
                                      · linarith only [h1963, hlam, p1960_0]
                                      · rcases p1960_3 (m.d 1 3) (by simp) with h1965 | h1965
                                        · linarith only [h1, h1965, hlam]
                                        · linarith only [h1319, h1965, hlam]
                                    · linarith only [h1962, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    rcases p1960_3 (m.d 0 1) (by simp) with h1969 | h1969
                                    · rcases p1960_3 (m.d 1 2) (by simp) with h1970 | h1970
                                      · linarith only [h0, h1970, hlam]
                                      · rcases p1960_3 (m.d 1 3) (by simp) with h1972 | h1972
                                        · linarith only [h1972, hlam, p1960_0]
                                        · rcases p1960_3 (m.d 1 4) (by simp) with h1974 | h1974
                                          · linarith only [h1974, h2, hlam]
                                          · linarith only [h1473, h1974, hlam]
                                    · linarith only [h1969, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1904, hc01, hc45, hlam, hphi, ht0b, ht5b, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    rcases p1960_3 (m.d 0 1) (by simp) with h1979 | h1979
                                    · rcases p1960_3 (m.d 1 2) (by simp) with h1980 | h1980
                                      · linarith only [h0, h1980, hlam]
                                      · rcases p1960_3 (m.d 1 3) (by simp) with h1982 | h1982
                                        · linarith only [h1, h1982, hlam]
                                        · rcases p1960_3 (m.d 1 4) (by simp) with h1984 | h1984
                                          · linarith only [h1984, h2, hlam]
                                          · linarith only [h1904, h1984, hlam]
                                    · linarith only [h1979, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h0, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1319, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1321, hlam, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1471, hlam, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1473, hlam, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1815, hlam, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h2, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1321, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1960_1, u2elo3]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1321, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1960_1, u2elo3]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h3, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1960_1]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1074, h1319, h1907, h3, hc12, hlam, hphi, p1960_1, u2elo3]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [h1904, hlam, p1960_0]
                                  · obtain ⟨p1960_0, p1960_1, p1960_2, p1960_3⟩ := h1960c
                                    linarith only [hlam, p1960_0]
                                · linarith only [h1074, h1907, h1909, hlam, ht01, ht12, u2elo3]
                              · linarith only [h1905, h1908, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1321, h1904, h1907, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2011 | h2011
                          · linarith only [h1319, h1473, h2011, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2013 | h2013
                            · linarith only [h1321, h1904, h2013, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2015 | h2015
                              · linarith only [h0, h2011, h2013, h2015, h4, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h2011, h2015, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2018 | h2018
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2019 | h2019
            · linarith only [h0, h2019, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2021 | h2021
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2022 | h2022
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2023 | h2023
                  · linarith only [h0, h2019, h2023, h3, hlam]
                  · linarith only [h0, h2021, h2023, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2026 | h2026
                  · linarith only [h0, h2019, h2026, hlam]
                  · linarith only [h2, h2021, h2022, h2026, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h2018, h2021, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2030 | h2030
            · linarith only [h0, h2018, h2030, h3, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2032 | h2032
              · linarith only [h0, h2018, h2032, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2034 | h2034
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2035 | h2035
                  · linarith only [h1, h2030, h2032, h2035, h3, hlam]
                  · linarith only [h1, h2032, h2034, h2035, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2038 | h2038
                  · linarith only [h0, h2030, h2038, hlam]
                  · linarith only [h1, h2032, h2038, h3, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2041 | h2041
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2042 | h2042
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2043 | h2043
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2044 | h2044
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2045 | h2045
                · linarith only [h0, h2, h2045, hlam]
                · linarith only [h0, h2, h2044, h2045, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h2042, h2044, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2049 | h2049
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2050 | h2050
                · linarith only [h0, h2, h2050, hlam]
                · linarith only [h0, h2, h2050, hc12, hlam, hphi, u2elo3]
              · linarith only [h2042, h2049, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2054 | h2054
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2055 | h2055
              · linarith only [h2042, h2055, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2057 | h2057
                · linarith only [h0, h2, h2042, h2057, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1, h2, h2055, h2057, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2060 | h2060
              · linarith only [h0, h2042, h2060, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2062 | h2062
                · linarith only [h1, h2, h2060, h2062, hlam]
                · linarith only [h1, h2, h2060, h2062, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2065 | h2065
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2066 | h2066
            · linarith only [h0, h2041, h2066, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2068 | h2068
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2069 | h2069
                · linarith only [h0, h2, h2069, hlam]
                · linarith only [h0, h2, h2068, h2069, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h2065, h2066, h2068, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2073 | h2073
            · linarith only [h1, h2041, h2065, h2073, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2075 | h2075
              · linarith only [h0, h2, h2065, h2075, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2077 | h2077
                · linarith only [h0, h2, h2065, h2077, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1, h2, h2075, h2077, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2080 | h2080
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2081 | h2081
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2082 | h2082
          · linarith only [h0, h1, h2082, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2084 | h2084
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2085 | h2085
              · linarith only [h0, h1, h2082, h2085, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2085, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2088 | h2088
              · linarith only [h0, h1, h2082, h2088, hlam]
              · linarith only [h0, h1, h2088, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2091 | h2091
          · linarith only [h0, h1, h2091, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2093 | h2093
            · linarith only [h0, h2081, h2093, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2095 | h2095
              · linarith only [h0, h1, h2091, h2095, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2095, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2098 | h2098
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2099 | h2099
          · linarith only [h0, h1, h2099, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2101 | h2101
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2102 | h2102
              · linarith only [h0, h1, h2099, h2102, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2102, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2105 | h2105
              · linarith only [h0, h1, h2099, h2105, hlam]
              · linarith only [h0, h1, h2105, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2108 | h2108
          · linarith only [h0, h1, h2108, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2110 | h2110
            · linarith only [h0, h2098, h2110, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2112 | h2112
              · linarith only [h0, h1, h2108, h2112, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2112, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2115 | h2115
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2116 | h2116
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2117 | h2117
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2118 | h2118
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2119 | h2119
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2120 | h2120
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2121 | h2121
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2122 | h2122
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2123 | h2123
                    · linarith only [h0, h2115, h2123, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2125 | h2125
                      · linarith only [h0, h2116, h2123, h2125, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2127 | h2127
                        · linarith only [h0, h2116, h2127, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2129 | h2129
                          · linarith only [h2120, h2123, h2129, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2131 | h2131
                            · linarith only [h2121, h2127, h2131, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2133 | h2133
                              · rcases h0emin with h2134 | h2134 | h2134 | h2134 | h2134
                                · linarith only [h0, h2134, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2134, hlam, ht01, ht12, u2elo0]
                                · linarith only [h0, h2115, h2134, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2116, h2134, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2117, h2134, hlam, ht01, ht12, u2elo1]
                              · rcases h0emin with h2140 | h2140 | h2140 | h2140 | h2140
                                · linarith only [h0, h2140, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2140, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2115, h2140, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2116, h2140, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2117, h2140, hlam, ht01, ht12, u2elo1]
                  · linarith only [h0, h2122, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2121, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2115, h2120, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h2117, h2119, hlam]
          · linarith only [h0, h2115, h2118, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2151 | h2151
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2152 | h2152
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2153 | h2153
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2154 | h2154
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2155 | h2155
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2156 | h2156
                    · linarith only [h2115, h2117, h2155, h2156, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2158 | h2158
                      · linarith only [h2116, h2117, h2155, h2156, h2158, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2160 | h2160
                        · linarith only [h2116, h2117, h2155, h2160, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2162 | h2162
                          · linarith only [h2153, h2156, h2162, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2164 | h2164
                            · linarith only [h2116, h2117, h2154, h2160, h2164, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2166 | h2166
                              · linarith only [h2116, h2117, h2156, h2160, h2166, hc13, hc34, hlam, hphi]
                              · rcases h0emin with h2168 | h2168 | h2168 | h2168 | h2168
                                · linarith only [h2117, h2155, h2168, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2168, hlam, ht01, ht12, u2elo0]
                                · linarith only [h2115, h2117, h2155, h2168, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2116, h2117, h2155, h2168, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2117, h2155, h2168, hlam, ht01, ht12, u2elo1]
                  · linarith only [h0, h2152, h2155, hlam]
                · linarith only [h0, h2116, h2154, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h2115, h2153, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2177 | h2177
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2178 | h2178
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2179 | h2179
                  · linarith only [h2152, h2179, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2115, h2177, h2179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2115, h2177, h2178, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2115, h2177, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h2115, h2151, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2185 | h2185
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2186 | h2186
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2187 | h2187
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2188 | h2188
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2189 | h2189
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2190 | h2190
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2191 | h2191
                    · linarith only [h0, h2115, h2191, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2193 | h2193
                      · linarith only [h2115, h2116, h2189, h2193, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2195 | h2195
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2196 | h2196
                          · linarith only [h2116, h2185, h2188, h2191, h2193, h2196, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2198 | h2198
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2199 | h2199
                              · rcases h0emin with h2200 | h2200 | h2200 | h2200 | h2200
                                · linarith only [h2116, h2189, h2200, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2200, hlam, ht01, ht12, u2elo0]
                                · linarith only [h2115, h2116, h2189, h2200, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2116, h2189, h2200, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2116, h2185, h2189, h2200, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2116, h2185, h2190, h2191, h2198, h2199, hlam]
                            · linarith only [h2116, h2185, h2189, h2195, h2198, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h2116, h2185, h2188, h2193, h2195, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h2116, h2189, h2190, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2185, h2189, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h2115, h2188, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h2185, h2187, hlam]
          · linarith only [h0, h2115, h2186, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2214 | h2214
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2215 | h2215
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2216 | h2216
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2217 | h2217
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2218 | h2218
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2219 | h2219
                    · linarith only [h2115, h2116, h2217, h2219, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2221 | h2221
                      · linarith only [h2115, h2116, h2217, h2221, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2223 | h2223
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2224 | h2224
                          · linarith only [h2115, h2185, h2216, h2219, h2223, h2224, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2226 | h2226
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2227 | h2227
                              · rcases h0emin with h2228 | h2228 | h2228 | h2228 | h2228
                                · linarith only [h2185, h2217, h2223, h2228, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2228, hlam, ht01, ht12, u2elo0]
                                · linarith only [h2115, h2185, h2217, h2223, h2228, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2116, h2217, h2228, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2185, h2217, h2223, h2228, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2185, h2217, h2219, h2223, h2226, h2227, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2235 | h2235
                              · rcases h0emin with h2236 | h2236 | h2236 | h2236 | h2236
                                · linarith only [h2185, h2223, h2236, hc14, hlam, ht01]
                                · linarith only [h0, h2236, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2185, h2223, h2236, hc14, hlam, ht01]
                                · linarith only [h2116, h2217, h2236, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2215, h2236, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2219, h2223, h2235, hlam]
                        · linarith only [h2115, h2116, h2216, h2223, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2115, h2216, h2218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2115, h2216, h2217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2216, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2247 | h2247
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2248 | h2248
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2249 | h2249
                  · linarith only [h2215, h2249, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2115, h2247, h2249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2115, h2247, h2248, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2247, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h0, h2115, h2214, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2255 | h2255
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2256 | h2256
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2257 | h2257
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2258 | h2258
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2259 | h2259
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2260 | h2260
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2261 | h2261
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2262 | h2262
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2263 | h2263
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2264 | h2264
                        · linarith only [h2115, h2255, h2259, h2264, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2266 | h2266
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2267 | h2267
                            · linarith only [h2260, h2264, h2267, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2269 | h2269
                              · linarith only [h2257, h2264, h2266, h2269, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0emin with h2271 | h2271 | h2271 | h2271 | h2271
                                · linarith only [h2115, h2259, h2271, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2271, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2259, h2271, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2255, h2259, h2271, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2256, h2259, h2271, hlam, ht01, ht12, u2elo1]
                          · linarith only [h2115, h2255, h2259, h2262, h2266, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h2115, h2256, h2263, hlam]
                    · linarith only [h2115, h2255, h2262, hlam]
                  · linarith only [h2115, h2259, h2261, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2115, h2259, h2260, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2255, h2257, h2259, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2256, h2258, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2284 | h2284
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2285 | h2285
              · linarith only [h0, h2257, h2285, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h2255, h2285, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h2256, h2284, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2289 | h2289
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2290 | h2290
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2291 | h2291
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2292 | h2292
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2293 | h2293
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2294 | h2294
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2295 | h2295
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2296 | h2296
                        · linarith only [h2255, h2256, h2291, h2295, h2296, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2298 | h2298
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2299 | h2299
                            · linarith only [h2255, h2256, h2292, h2296, h2299, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2301 | h2301
                              · linarith only [h2256, h2289, h2296, h2298, h2301, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h0emin with h2303 | h2303 | h2303 | h2303 | h2303
                                · linarith only [h2256, h2291, h2295, h2303, hc12, hlam, ht01]
                                · linarith only [h2303, hlam, ht01, ht12, u2elo0]
                                · linarith only [h2115, h2291, h2303, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2255, h2291, h2303, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2290, h2303, hlam, ht01, ht12, u2elo1]
                          · linarith only [h2255, h2256, h2291, h2294, h2295, h2298, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2310 | h2310
                        · linarith only [h0, h2255, h2310, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2312 | h2312
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2313 | h2313
                            · linarith only [h2115, h2255, h2292, h2295, h2310, h2313, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2315 | h2315
                              · linarith only [h2115, h2295, h2310, h2312, h2315, hc01, hlam, hphi, ht12, u2elo2]
                              · linarith only [h2115, h2255, h2292, h2295, h2312, h2315, hc34, hc45, hlam, hphi]
                          · linarith only [h2294, h2295, h2312, hc23, hc35, hlam, hphi]
                    · linarith only [h2115, h2255, h2294, hlam]
                  · linarith only [h0, h2290, h2293, hlam]
                · linarith only [h0, h2292, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2255, h2291, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2323 | h2323
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2324 | h2324
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2325 | h2325
                  · linarith only [h2290, h2325, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2255, h2324, h2325, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h2115, h2323, h2324, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2255, h2323, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2330 | h2330
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2331 | h2331
              · linarith only [h2289, h2330, h2331, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h2255, h2331, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2334 | h2334
              · linarith only [h2289, h2334, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h2255, h2334, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2337 | h2337
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2338 | h2338
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2339 | h2339
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2340 | h2340
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2341 | h2341
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2342 | h2342
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2343 | h2343
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2344 | h2344
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2345 | h2345
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2346 | h2346
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2347 | h2347
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2348 | h2348
                              · linarith only [h2338, h2346, h2348, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h2337, h2342, h2347, h2348, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h2255, h2337, h2340, h2343, h2345, h2347, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2352 | h2352
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2353 | h2353
                              · rcases h0emin with h2354 | h2354 | h2354 | h2354 | h2354
                                · linarith only [h2255, h2340, h2343, h2354, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2354, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2340, h2354, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2340, h2343, h2354, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2337, h2340, h2343, h2354, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2346, h2352, h2353, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · linarith only [h2255, h2337, h2340, h2343, h2345, h2352, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h2255, h2337, h2345, hlam]
                      · linarith only [h2255, h2337, h2343, h2344, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2364 | h2364
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2365 | h2365
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2366 | h2366
                          · linarith only [h2115, h2343, h2366, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2368 | h2368
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2369 | h2369
                              · rcases h0emin with h2370 | h2370 | h2370 | h2370 | h2370
                                · linarith only [h2115, h2343, h2370, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h0, h2370, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2343, h2370, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h2255, h2341, h2370, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2337, h2343, h2370, hc34, hlam, ht01, ht12, ht23]
                              · linarith only [h2115, h2337, h2341, h2342, h2343, h2368, h2369, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h2115, h2337, h2343, h2365, h2366, h2368, hc23, hc34, hlam, hphi]
                        · linarith only [h2115, h2337, h2343, h2365, hlam]
                      · linarith only [h2115, h2337, h2364, hlam]
                  · linarith only [h0, h2342, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2115, h2340, h2341, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2337, h2340, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h0, h2337, h2339, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2384 | h2384
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2385 | h2385
              · linarith only [h2338, h2384, h2385, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h2337, h2385, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h0, h2337, h2384, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2389 | h2389
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2390 | h2390
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2391 | h2391
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2392 | h2392
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2393 | h2393
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2394 | h2394
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2395 | h2395
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2396 | h2396
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2397 | h2397
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2398 | h2398
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2399 | h2399
                              · linarith only [h2389, h2397, h2399, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h2389, h2397, h2398, h2399, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2402 | h2402
                              · linarith only [h2397, h2398, h2402, hlam]
                              · rcases h0emin with h2404 | h2404 | h2404 | h2404 | h2404
                                · linarith only [h2337, h2404, hc15, hlam, ht01]
                                · linarith only [h0, h2404, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2389, h2404, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2392, h2404, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2390, h2404, hlam, ht01, ht12, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2410 | h2410
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2411 | h2411
                              · rcases h0emin with h2412 | h2412 | h2412 | h2412 | h2412
                                · linarith only [h2337, h2391, h2394, h2396, h2412, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2412, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2389, h2412, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2391, h2394, h2412, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2337, h2391, h2394, h2396, h2412, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2391, h2394, h2396, h2397, h2411, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2419 | h2419
                              · linarith only [h2391, h2394, h2410, h2419, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h2391, h2394, h2396, h2397, h2419, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2422 | h2422
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2423 | h2423
                            · linarith only [h2255, h2396, h2423, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2425 | h2425
                              · linarith only [h2255, h2396, h2422, h2425, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases h0emin with h2427 | h2427 | h2427 | h2427 | h2427
                                · linarith only [h2255, h2427, hc14, hlam, ht01]
                                · linarith only [h0, h2427, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2389, h2427, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2396, h2427, hc45, hlam, ht01, ht12, ht23, ht34]
                                · linarith only [h0, h2390, h2427, hlam, ht01, ht12, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2433 | h2433
                            · linarith only [h2255, h2396, h2433, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2435 | h2435
                              · linarith only [h2255, h2391, h2394, h2396, h2435, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases h0emin with h2437 | h2437 | h2437 | h2437 | h2437
                                · linarith only [h2255, h2437, hc14, hlam, ht01]
                                · linarith only [h0, h2437, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2389, h2437, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2391, h2395, h2396, h2422, h2435, h2437, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u2elo1]
                                · linarith only [h0, h2390, h2437, hlam, ht01, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2443 | h2443
                        · linarith only [h2394, h2395, h2443, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2445 | h2445
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2446 | h2446
                            · linarith only [h2255, h2443, h2445, h2446, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2448 | h2448
                              · linarith only [h2255, h2443, h2448, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h0emin with h2450 | h2450 | h2450 | h2450 | h2450
                                · linarith only [h2255, h2394, h2450, hc13, hlam, ht01]
                                · linarith only [h0, h2450, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2395, h2448, h2450, hc45, hlam, ht01, ht12, ht23, ht34]
                                · linarith only [h2255, h2394, h2395, h2448, h2450, hc45, hlam, ht01, ht12, ht23, ht34]
                                · linarith only [h0, h2390, h2450, hlam, ht01, ht12, u2elo1]
                          · linarith only [h2394, h2395, h2445, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2457 | h2457
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2458 | h2458
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2459 | h2459
                          · linarith only [h2394, h2457, h2459, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2461 | h2461
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2462 | h2462
                              · rcases h0emin with h2463 | h2463 | h2463 | h2463 | h2463
                                · linarith only [h2337, h2457, h2463, hc13, hlam, ht01]
                                · linarith only [h0, h2463, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2394, h2463, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h2255, h2392, h2463, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2337, h2394, h2457, h2463, hc34, hlam, ht01, ht12, ht23]
                              · linarith only [h2392, h2461, h2462, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2470 | h2470
                              · linarith only [h2394, h2457, h2459, h2461, h2470, hc23, hc34, hlam, hphi]
                              · linarith only [h2337, h2392, h2394, h2457, h2458, h2470, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h2394, h2457, h2458, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2474 | h2474
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2475 | h2475
                          · linarith only [h2115, h2394, h2475, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2477 | h2477
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2478 | h2478
                              · rcases h0emin with h2479 | h2479 | h2479 | h2479 | h2479
                                · linarith only [h2115, h2479, hc13, hlam, ht01]
                                · linarith only [h0, h2479, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2457, h2478, h2479, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h2255, h2392, h2479, hlam, ht01, ht12, u2elo1]
                                · linarith only [h0, h2390, h2479, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2392, h2477, h2478, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2486 | h2486
                              · rcases h0emin with h2487 | h2487 | h2487 | h2487 | h2487
                                · linarith only [h2115, h2392, h2457, h2474, h2475, h2477, h2486, h2487, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                                · linarith only [h0, h2487, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2115, h2392, h2457, h2474, h2475, h2477, h2486, h2487, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                                · linarith only [h2255, h2392, h2487, hlam, ht01, ht12, u2elo1]
                                · linarith only [h2337, h2392, h2474, h2487, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2115, h2392, h2394, h2474, h2486, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2494 | h2494
                          · linarith only [h2115, h2394, h2494, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2496 | h2496
                            · linarith only [h2255, h2474, h2496, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2498 | h2498
                              · linarith only [h2115, h2394, h2474, h2498, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h2115, h2394, h2498, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h2390, h2393, hlam]
                · linarith only [h0, h2392, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2391, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2504 | h2504
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2505 | h2505
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2506 | h2506
                  · linarith only [h2390, h2506, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2506, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2115, h2504, h2505, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h2389, h2504, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2511 | h2511
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2512 | h2512
              · linarith only [h2389, h2512, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h2512, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2515 | h2515
              · linarith only [h2389, h2515, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h2515, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 8592000 in
theorem n7l_sAA2_M_LI_M_LI_L_I (m : N7Model)
    (h0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (h1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  obtain ⟨h0elo, _, _, _⟩ := h0
  obtain ⟨h1elo, _, _, h1bigk⟩ := h1
  obtain ⟨h2bigk, _, _⟩ := h2
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h11, h14, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h17, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h11, h17, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h11, h12, h20, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h22, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h11, h12, h20, h22, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                              · linarith only [h0, h11, h25, h27, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                                · linarith only [h0, h27, h29, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h11, h25, h29, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h11, h25, h26, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                              · linarith only [h0, h11, h34, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                                · linarith only [h25, h36, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                                  · linarith only [h0, h38, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h2, h33, h38, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                              · linarith only [h11, h41, h8, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                                · linarith only [h25, h43, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                                  · linarith only [h0, h33, h45, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                                    · rcases h1bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h10, hc25, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        rcases p48_3 (m.d 0 1) (by simp) with h51 | h51
                                        · rcases p48_3 (m.d 1 2) (by simp) with h52 | h52
                                          · linarith only [h0, h52, hlam]
                                          · linarith only [h52, h8, hlam]
                                        · linarith only [h51, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        rcases p48_3 (m.d 0 1) (by simp) with h56 | h56
                                        · rcases p48_3 (m.d 1 2) (by simp) with h57 | h57
                                          · linarith only [h0, h57, hlam]
                                          · linarith only [h57, h9, hlam]
                                        · linarith only [h56, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        rcases p48_3 (m.d 0 1) (by simp) with h61 | h61
                                        · rcases p48_3 (m.d 1 2) (by simp) with h62 | h62
                                          · linarith only [h0, h62, hlam]
                                          · linarith only [h10, h62, hlam]
                                        · linarith only [h61, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h0, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h0, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1, u1elo0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h0, h11, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1, u1elo0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h1, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h8, hlam, p48_1]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h11, hlam, p48_1]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h25, hlam, p48_1]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h2, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h9, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h33, h47, h8, hc23, hc34, hlam, hphi, p48_1]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h33, hlam, p48_1]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h3, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h10, hlam, p48_0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h3, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1, u1elo0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [h0, h33, h5, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p48_1, u1elo0]
                                      · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                                        linarith only [hlam, p48_0]
                                    · linarith only [h0, h11, h47, h5, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h10, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h4, h8, h89, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h0, h4, h8, h91, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                                    · linarith only [h1, h93, h99, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h0, h4, h8, h93, h95, h99, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h4, h8, h93, h95, h98, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h8, h94, h97, hlam]
                              · linarith only [h8, h93, h96, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                                  · linarith only [h0, h107, h5, h95, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h107, h5, h7, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h106, h8, h94, hlam]
                              · linarith only [h105, h8, h93, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                            · linarith only [h112, h93, h94, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                                · linarith only [h0, h115, h4, h94, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                                  · linarith only [h0, h112, h117, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h117, h5, h7, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h1, h114, h93, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                              · linarith only [h0, h123, h4, h93, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                                    · rcases h1bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        rcases p128_3 (m.d 0 1) (by simp) with h130 | h130
                                        · rcases p128_3 (m.d 1 2) (by simp) with h131 | h131
                                          · linarith only [h131, hlam, p128_0]
                                          · rcases p128_3 (m.d 1 3) (by simp) with h133 | h133
                                            · linarith only [h1, h133, hlam]
                                            · linarith only [h133, h8, hlam]
                                        · linarith only [h130, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h121, h127, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h121, h127, h93, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        rcases p128_3 (m.d 0 1) (by simp) with h139 | h139
                                        · rcases p128_3 (m.d 1 2) (by simp) with h140 | h140
                                          · linarith only [h0, h140, hlam]
                                          · rcases p128_3 (m.d 1 3) (by simp) with h142 | h142
                                            · linarith only [h1, h142, hlam]
                                            · linarith only [h121, h142, hlam]
                                        · linarith only [h139, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h8, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h89, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h91, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h1, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h93, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h123, h5, h8, hc15, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h2, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h5, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h5, h89, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h5, h89, h91, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h3, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h121, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h122, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                    · linarith only [h0, h123, h127, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h122, h126, h89, hlam]
                                · linarith only [h1, h121, h125, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h121, h122, h5, h7, h93, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                              · linarith only [h0, h171, h4, h93, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                                · linarith only [h0, h121, h171, h173, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
                                    · rcases h1bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        rcases p177_3 (m.d 0 1) (by simp) with h179 | h179
                                        · rcases p177_3 (m.d 1 2) (by simp) with h180 | h180
                                          · linarith only [h180, hlam, p177_0]
                                          · rcases p177_3 (m.d 1 3) (by simp) with h182 | h182
                                            · linarith only [h1, h182, hlam]
                                            · linarith only [h182, h8, hlam]
                                        · linarith only [h179, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        rcases p177_3 (m.d 0 1) (by simp) with h186 | h186
                                        · rcases p177_3 (m.d 1 2) (by simp) with h187 | h187
                                          · linarith only [h0, h187, hlam]
                                          · rcases p177_3 (m.d 1 3) (by simp) with h189 | h189
                                            · linarith only [h189, hlam, p177_0]
                                            · rcases p177_3 (m.d 1 4) (by simp) with h191 | h191
                                              · linarith only [h191, h2, hlam]
                                              · linarith only [h191, h93, hlam]
                                        · linarith only [h186, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h170, hc45, hlam, hphi, ht01, ht0b, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        rcases p177_3 (m.d 0 1) (by simp) with h196 | h196
                                        · rcases p177_3 (m.d 1 2) (by simp) with h197 | h197
                                          · linarith only [h0, h197, hlam]
                                          · rcases p177_3 (m.d 1 3) (by simp) with h199 | h199
                                            · linarith only [h1, h199, hlam]
                                            · rcases p177_3 (m.d 1 4) (by simp) with h201 | h201
                                              · linarith only [h2, h201, hlam]
                                              · linarith only [h170, h201, hlam]
                                        · linarith only [h196, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h0, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h8, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h89, hlam, p177_1]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h91, hlam, p177_1]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h1, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h93, hlam, p177_1]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h121, hlam, p177_1]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h2, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h0, h5, h89, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h0, h5, h89, hc15, hlam, hphi, ht01, ht0b, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h3, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h0, h175, h5, h8, h91, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p177_1, u1elo0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [h170, hlam, p177_0]
                                      · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                        linarith only [hlam, p177_0]
                                    · linarith only [h0, h176, h5, h7, h8, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h170, h175, h89, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                              · linarith only [h0, h227, h4, h8, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                                · linarith only [h0, h121, h227, h229, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                                  · linarith only [h0, h170, h231, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h227, h231, h5, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                            · linarith only [h2, h239, h7, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                              · linarith only [h0, h234, h241, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h237, h241, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                            · linarith only [h2, h244, h7, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                              · linarith only [h0, h234, h246, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h237, h238, h246, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                            · linarith only [h2, h250, h7, hlam]
                            · linarith only [h237, h249, h250, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h253 | h253
                            · linarith only [h2, h253, h7, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                              · linarith only [h0, h237, h255, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                                · linarith only [h0, h234, h249, h253, h257, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
                                  · linarith only [h0, h2, h234, h237, h259, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
                                    · rcases h1bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h234, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p262_1, u1elo0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        rcases p262_3 (m.d 0 1) (by simp) with h265 | h265
                                        · rcases p262_3 (m.d 1 2) (by simp) with h266 | h266
                                          · linarith only [h0, h266, hlam]
                                          · linarith only [h234, h266, hlam]
                                        · linarith only [h265, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        rcases p262_3 (m.d 0 1) (by simp) with h270 | h270
                                        · rcases p262_3 (m.d 1 2) (by simp) with h271 | h271
                                          · linarith only [h0, h271, hlam]
                                          · linarith only [h235, h271, hlam]
                                        · linarith only [h270, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        rcases p262_3 (m.d 0 1) (by simp) with h275 | h275
                                        · rcases p262_3 (m.d 1 2) (by simp) with h276 | h276
                                          · linarith only [h0, h276, hlam]
                                          · linarith only [h236, h276, hlam]
                                        · linarith only [h275, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h0, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h0, h234, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p262_1, u1elo0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h0, h234, h237, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p262_1, u1elo0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h0, h234, h237, h253, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p262_1, u1elo0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h1, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h234, hlam, p262_1]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h237, hlam, p262_1]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h249, hlam, p262_1]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h2, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h235, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h2, h234, h261, h7, hc23, hc34, hlam, hphi, p262_1]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h253, hlam, p262_1]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h3, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h236, hlam, p262_0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h234, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p262_1, u1elo0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [h0, h236, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p262_1, u1elo0]
                                      · obtain ⟨p262_0, p262_1, p262_2, p262_3⟩ := h262c
                                        linarith only [hlam, p262_0]
                                    · rcases h1bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h234, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        rcases p300_3 (m.d 0 1) (by simp) with h303 | h303
                                        · rcases p300_3 (m.d 1 2) (by simp) with h304 | h304
                                          · linarith only [h0, h304, hlam]
                                          · linarith only [h234, h304, hlam]
                                        · linarith only [h303, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        rcases p300_3 (m.d 0 1) (by simp) with h308 | h308
                                        · rcases p300_3 (m.d 1 2) (by simp) with h309 | h309
                                          · linarith only [h0, h309, hlam]
                                          · linarith only [h235, h309, hlam]
                                        · linarith only [h308, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        rcases p300_3 (m.d 0 1) (by simp) with h313 | h313
                                        · rcases p300_3 (m.d 1 2) (by simp) with h314 | h314
                                          · linarith only [h0, h314, hlam]
                                          · linarith only [h236, h314, hlam]
                                        · linarith only [h313, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h234, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h235, h255, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h234, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h237, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h249, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h235, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, h234, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h253, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h3, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h236, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h234, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h236, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p300_1, u1elo0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                      · linarith only [h0, h234, h236, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h234, h235, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h340 | h340
                    · linarith only [h0, h234, h340, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                      · linarith only [h0, h234, h342, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                            · linarith only [h340, h346, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                                  · linarith only [h350, h5, h7, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                                    · linarith only [h340, h344, h352, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                    · rcases h1bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        rcases p354_3 (m.d 0 1) (by simp) with h356 | h356
                                        · rcases p354_3 (m.d 1 2) (by simp) with h357 | h357
                                          · linarith only [h357, hlam, p354_0]
                                          · rcases p354_3 (m.d 1 3) (by simp) with h359 | h359
                                            · linarith only [h1, h359, hlam]
                                            · linarith only [h234, h359, hlam]
                                        · linarith only [h356, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h345, h352, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        rcases p354_3 (m.d 0 1) (by simp) with h364 | h364
                                        · rcases p354_3 (m.d 1 2) (by simp) with h365 | h365
                                          · linarith only [h0, h365, hlam]
                                          · rcases p354_3 (m.d 1 3) (by simp) with h367 | h367
                                            · linarith only [h1, h367, hlam]
                                            · linarith only [h344, h367, hlam]
                                        · linarith only [h364, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        rcases p354_3 (m.d 0 1) (by simp) with h371 | h371
                                        · rcases p354_3 (m.d 1 2) (by simp) with h372 | h372
                                          · linarith only [h0, h372, hlam]
                                          · rcases p354_3 (m.d 1 3) (by simp) with h374 | h374
                                            · linarith only [h1, h374, hlam]
                                            · linarith only [h345, h374, hlam]
                                        · linarith only [h371, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h0, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h234, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h340, hlam, p354_1]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h342, hlam, p354_1]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h1, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h0, h234, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h0, h234, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h2, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h344, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h346, hlam, p354_1]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h3, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h345, hlam, p354_0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p354_1, u1elo0]
                                      · obtain ⟨p354_0, p354_1, p354_2, p354_3⟩ := h354c
                                        linarith only [hlam, p354_0]
                                · linarith only [h234, h345, h349, hlam]
                              · linarith only [h234, h344, h348, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h400 | h400
                            · linarith only [h340, h400, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h402 | h402
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h403 | h403
                                · linarith only [h0, h345, h4, h403, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                                  · linarith only [h405, h5, h7, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                                    · linarith only [h344, h407, h7, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · rcases h1bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        rcases p409_3 (m.d 0 1) (by simp) with h411 | h411
                                        · rcases p409_3 (m.d 1 2) (by simp) with h412 | h412
                                          · linarith only [h412, hlam, p409_0]
                                          · rcases p409_3 (m.d 1 3) (by simp) with h414 | h414
                                            · linarith only [h1, h414, hlam]
                                            · linarith only [h234, h414, hlam]
                                        · linarith only [h411, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h344, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        rcases p409_3 (m.d 0 1) (by simp) with h419 | h419
                                        · rcases p409_3 (m.d 1 2) (by simp) with h420 | h420
                                          · linarith only [h0, h420, hlam]
                                          · rcases p409_3 (m.d 1 3) (by simp) with h422 | h422
                                            · linarith only [h1, h422, hlam]
                                            · linarith only [h344, h422, hlam]
                                        · linarith only [h419, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h344, h345, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h0, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h234, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h340, hlam, p409_1]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h342, hlam, p409_1]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h1, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h0, h234, h403, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h345, hlam, p409_1]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h2, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h344, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h400, hlam, p409_1]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h3, hlam, p409_0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h0, h342, h6, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [h0, h340, h342, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u1elo0]
                                      · obtain ⟨p409_0, p409_1, p409_2, p409_3⟩ := h409c
                                        linarith only [hlam, p409_0]
                              · linarith only [h1, h344, h402, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                            · linarith only [h2, h449, h7, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h344, h448, h449, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h452 | h452
                            · linarith only [h340, h452, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                              · linarith only [h0, h344, h4, h454, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                                · linarith only [h234, h448, h454, h456, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                                  · linarith only [h0, h458, h5, h7, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                                    · linarith only [h234, h454, h460, h5, h7, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h234, h454, h460, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
                · linarith only [h463, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h466 | h466
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h467 | h467
                      · linarith only [h0, h467, h6, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
                          · linarith only [h465, h467, h470, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h472 | h472
                            · linarith only [h2, h463, h472, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h474 | h474
                              · linarith only [h0, h465, h474, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h469, h474, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                          · linarith only [h465, h467, h477, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                            · linarith only [h2, h463, h479, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                              · linarith only [h4, h469, h481, h6, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
                                · linarith only [h467, h477, h481, h483, h5, h6, hc12, hc25, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h485 | h485
                                  · linarith only [h3, h463, h466, h467, h485, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h487 | h487
                                    · linarith only [h0, h466, h481, h485, h487, h6, hc23, hc34, hlam, hphi]
                                    · rcases h1bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h466, h481, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        rcases p489_3 (m.d 0 1) (by simp) with h492 | h492
                                        · rcases p489_3 (m.d 1 2) (by simp) with h493 | h493
                                          · linarith only [h0, h493, hlam]
                                          · linarith only [h465, h493, hlam]
                                        · linarith only [h492, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        rcases p489_3 (m.d 0 1) (by simp) with h497 | h497
                                        · rcases p489_3 (m.d 1 2) (by simp) with h498 | h498
                                          · linarith only [h0, h498, hlam]
                                          · linarith only [h466, h498, hlam]
                                        · linarith only [h497, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h466, h467, h481, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h0, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h0, h465, h483, h6, hc23, hc35, hlam, hphi, p489_1]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h3, h467, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h467, hlam, p489_1]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h1, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h465, hlam, p489_1]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h469, hlam, p489_1]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h477, hlam, p489_1]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h2, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h466, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h2, h465, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h479, hlam, p489_1]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h3, hlam, p489_0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h3, h465, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p489_1, u1elo0]
                                      · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                                        linarith only [hlam, p489_0]
                    · linarith only [h466, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h4, h465, h6, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h525 | h525
              · rcases m.htr 0 4 5 (by decide) (by decide) with h526 | h526
                · rcases m.htr 1 2 3 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h528 | h528
                    · linarith only [h0, h5, h528, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h530 | h530
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
                        · linarith only [h527, h528, h531, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h533 | h533
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h534 | h534
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                              · linarith only [h4, h5, h531, h535, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                                · linarith only [h2, h527, h528, h537, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h1, h533, h537, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h2, h526, h527, h528, h533, h534, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h541 | h541
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                              · linarith only [h0, h527, h542, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h544 | h544
                                · linarith only [h527, h533, h544, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h547 | h547
                                    · rcases h1bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h527, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        rcases p548_3 (m.d 0 1) (by simp) with h551 | h551
                                        · rcases p548_3 (m.d 1 2) (by simp) with h552 | h552
                                          · linarith only [h0, h552, hlam]
                                          · linarith only [h527, h552, hlam]
                                        · linarith only [h551, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h528, h530, h544, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        rcases p548_3 (m.d 0 1) (by simp) with h557 | h557
                                        · rcases p548_3 (m.d 1 2) (by simp) with h558 | h558
                                          · linarith only [h0, h558, hlam]
                                          · linarith only [h530, h558, hlam]
                                        · linarith only [h557, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h0, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h528, hlam, p548_1]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h2, h527, h528, h533, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h1, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h527, hlam, p548_1]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h531, hlam, p548_1]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h533, hlam, p548_1]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h2, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h2, h527, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h2, h527, h533, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h3, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h530, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h3, h527, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u1elo0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [h541, hlam, p548_0]
                                      · obtain ⟨p548_0, p548_1, p548_2, p548_3⟩ := h548c
                                        linarith only [hlam, p548_0]
                                    · linarith only [h4, h5, h542, h547, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h2, h5, h541, h546, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h2, h526, h528, h530, h541, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h5, h525, h527, h530, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h4, h5, h527, hc12, hc24, hlam, hphi]
                · linarith only [h5, h525, h526, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h588 | h588
                · rcases m.htr 1 2 3 (by decide) (by decide) with h589 | h589
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h590 | h590
                    · linarith only [h0, h5, h590, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
                      · linarith only [h0, h525, h592, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                        · linarith only [h589, h590, h594, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
                          · linarith only [h589, h592, h596, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h598 | h598
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h599 | h599
                              · linarith only [h4, h525, h588, h594, h599, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                                · linarith only [h589, h592, h596, h601, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
                                    · rcases h1bigk with h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h589, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        rcases p605_3 (m.d 0 1) (by simp) with h608 | h608
                                        · rcases p605_3 (m.d 1 2) (by simp) with h609 | h609
                                          · linarith only [h0, h609, hlam]
                                          · linarith only [h589, h609, hlam]
                                        · linarith only [h608, hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h589, h592, h598, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h589, h592, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h0, hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h0, h589, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h590, hlam, p605_1]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h592, hlam, p605_1]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h1, hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h589, hlam, p605_1]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h594, hlam, p605_1]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h596, hlam, p605_1]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h2, hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h2, h589, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h3, hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h589, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo4]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h3, h589, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [h598, hlam, p605_0]
                                      · obtain ⟨p605_0, p605_1, p605_2, p605_3⟩ := h605c
                                        linarith only [hlam, p605_0]
                                    · linarith only [h0, h525, h589, h599, h603, h604, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h0, h2, h5, h589, h598, h603, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h588, h589, h590, h598, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h4, h5, h589, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h640 | h640
                    · linarith only [h0, h5, h640, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h642 | h642
                      · linarith only [h0, h525, h642, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
                        · linarith only [h639, h640, h644, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                          · linarith only [h639, h642, h646, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h648 | h648
                            · linarith only [h2, h588, h648, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                              · linarith only [h3, h639, h640, h644, h648, h650, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                                · linarith only [h0, h639, h646, h648, h652, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h654 | h654
                                  · linarith only [h0, h5, h588, h639, h650, h654, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h5, h639, h654, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h4, h5, h639, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h658 | h658
            · rcases m.htr 0 2 5 (by decide) (by decide) with h659 | h659
              · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                  · linarith only [h4, h658, h661, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h670 | h670
                                  · linarith only [h0, h663, h670, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h1, h661, h663, h667, h668, h670, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h1, h4, h666, h669, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h1, h4, h663, h665, h667, h668, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h675 | h675
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h676 | h676
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h677 | h677
                                  · linarith only [h663, h667, h677, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
                                    · linarith only [h663, h667, h675, h679, hlam]
                                    · rcases h1bigk with h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h663, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h661, h663, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        rcases p681_3 (m.d 0 1) (by simp) with h685 | h685
                                        · rcases p681_3 (m.d 1 2) (by simp) with h686 | h686
                                          · linarith only [h0, h686, hlam]
                                          · linarith only [h663, h686, hlam]
                                        · linarith only [h685, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        rcases p681_3 (m.d 0 1) (by simp) with h690 | h690
                                        · rcases p681_3 (m.d 1 2) (by simp) with h691 | h691
                                          · linarith only [h0, h691, hlam]
                                          · linarith only [h664, h691, hlam]
                                        · linarith only [h690, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h0, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h661, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h0, h663, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h1, h661, h663, h667, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h1, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h1, h663, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h1, h663, h667, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h2, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h663, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h665, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h667, hlam, p681_1]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h3, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h664, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h666, hlam, p681_0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [h3, h663, h675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p681_1, u1elo0]
                                      · obtain ⟨p681_0, p681_1, p681_2, p681_3⟩ := h681c
                                        linarith only [hlam, p681_0]
                                · linarith only [h4, h658, h660, h663, h667, h675, h676, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h4, h658, h660, h663, h667, h675, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h661, h664, h666, hlam]
                        · linarith only [h661, h663, h665, hlam]
                      · linarith only [h4, h659, h664, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h658, h663, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                  · linarith only [h4, h658, h721, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h726 | h726
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h727 | h727
                            · linarith only [h2, h660, h727, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h730 | h730
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                                  · linarith only [h660, h723, h731, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                                    · linarith only [h2, h660, h723, h729, h733, hlam]
                                    · rcases h1bigk with h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h724, h731, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h721, h724, h729, h731, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        rcases p735_3 (m.d 0 1) (by simp) with h739 | h739
                                        · rcases p735_3 (m.d 1 2) (by simp) with h740 | h740
                                          · linarith only [h0, h740, hlam]
                                          · linarith only [h723, h740, hlam]
                                        · linarith only [h739, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        rcases p735_3 (m.d 0 1) (by simp) with h744 | h744
                                        · rcases p735_3 (m.d 1 2) (by simp) with h745 | h745
                                          · linarith only [h0, h745, hlam]
                                          · linarith only [h724, h745, hlam]
                                        · linarith only [h744, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h0, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h721, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h0, h723, h729, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h1, h721, h723, h727, h729, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h1, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h1, h723, h729, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h1, h723, h727, h729, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h2, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h723, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h725, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h727, hlam, p735_1]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h3, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h724, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h726, hlam, p735_0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [h3, h723, h729, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo0]
                                      · obtain ⟨p735_0, p735_1, p735_2, p735_3⟩ := h735c
                                        linarith only [hlam, p735_0]
                                · linarith only [h0, h1, h4, h723, h726, h729, h730, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h1, h4, h723, h725, h729, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h721, h724, h726, hlam]
                        · linarith only [h721, h723, h725, hlam]
                      · linarith only [h4, h659, h724, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h658, h723, hc12, hc23, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h775 | h775
                · linarith only [h658, h659, h775, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
                  · linarith only [h4, h658, h777, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h780 | h780
                      · linarith only [h0, h659, h780, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h782 | h782
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h783 | h783
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h784 | h784
                            · linarith only [h2, h775, h784, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h788 | h788
                                  · linarith only [h0, h659, h775, h779, h788, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h790 | h790
                                    · linarith only [h0, h659, h779, h786, h788, h790, hlam]
                                    · rcases h1bigk with h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h779, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h779, h780, h783, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        rcases p792_3 (m.d 0 1) (by simp) with h796 | h796
                                        · rcases p792_3 (m.d 1 2) (by simp) with h797 | h797
                                          · linarith only [h0, h797, hlam]
                                          · linarith only [h779, h797, hlam]
                                        · linarith only [h796, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h779, h780, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h0, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h777, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h0, h659, h779, h786, h788, hc34, hc45, hlam, hphi, p792_1]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h780, hlam, p792_1]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h1, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h1, h779, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h2, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h779, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h782, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h784, hlam, p792_1]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h3, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h779, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p792_1, u1elo4]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h783, hlam, p792_0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [h1, h779, h783, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p792_1, u1elo0]
                                      · obtain ⟨p792_0, p792_1, p792_2, p792_3⟩ := h792c
                                        linarith only [hlam, p792_0]
                                · linarith only [h1, h4, h783, h787, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h1, h4, h779, h782, h786, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h824 | h824
                            · linarith only [h2, h775, h824, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h826 | h826
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h827 | h827
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h828 | h828
                                  · linarith only [h0, h775, h779, h828, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                                    · linarith only [h2, h659, h779, h826, h828, h830, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                    · rcases h1bigk with h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h779, h826, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p832_1, u1elo0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h777, h779, h826, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p832_1, u1elo0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        rcases p832_3 (m.d 0 1) (by simp) with h836 | h836
                                        · rcases p832_3 (m.d 1 2) (by simp) with h837 | h837
                                          · linarith only [h0, h837, hlam]
                                          · linarith only [h779, h837, hlam]
                                        · linarith only [h836, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h779, h780, h826, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p832_1, u1elo0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h0, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h777, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h777, h783, h827, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h780, hlam, p832_1]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h1, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h783, h827, hc12, hc23, hlam, hphi, p832_1]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h779, h783, h826, h827, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h783, hlam, p832_1]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h2, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h779, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h782, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h824, hlam, p832_1]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h3, hlam, p832_0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h779, h826, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p832_1, u1elo4]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p832_1, u1elo0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [h3, h779, h826, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p832_1, u1elo0]
                                      · obtain ⟨p832_0, p832_1, p832_2, p832_3⟩ := h832c
                                        linarith only [hlam, p832_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h862 | h862
                                  · linarith only [h0, h779, h862, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h864 | h864
                                    · linarith only [h0, h4, h779, h826, h827, h862, h864, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                    · linarith only [h0, h4, h779, h827, h864, hc24, hc45, hlam, hphi]
                              · linarith only [h0, h3, h4, h779, h782, h783, h826, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h777, h779, h782, hlam]
                    · linarith only [h4, h658, h779, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h870 | h870
              · rcases m.htr 0 4 5 (by decide) (by decide) with h871 | h871
                · rcases m.htr 1 2 3 (by decide) (by decide) with h872 | h872
                  · linarith only [h4, h870, h872, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h874 | h874
                    · linarith only [h0, h658, h874, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h876 | h876
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h879 | h879
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h880 | h880
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h881 | h881
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h882 | h882
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h883 | h883
                                    · linarith only [h1, h877, h883, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h877, h879, h883, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h658, h877, h879, h882, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h1, h4, h878, h881, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h1, h4, h876, h877, h880, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h2, h871, h874, h876, h879, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h872, h876, h878, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h891 | h891
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h893 | h893
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h894 | h894
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h895 | h895
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                                    · rcases h1bigk with h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h876, h894, h896, hc45, hlam, hphi, ht01, ht0b, ht5b, p897_1, u1elo0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h872, h876, h894, h896, hc45, hlam, hphi, ht01, ht0b, ht5b, p897_1, u1elo0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h874, h876, h894, h896, hc45, hlam, hphi, ht01, ht0b, ht5b, p897_1, u1elo0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        rcases p897_3 (m.d 0 1) (by simp) with h902 | h902
                                        · rcases p897_3 (m.d 1 2) (by simp) with h903 | h903
                                          · linarith only [h0, h903, hlam]
                                          · linarith only [h876, h903, hlam]
                                        · linarith only [h902, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h0, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h872, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h874, hlam, p897_1]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h872, h877, h893, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p897_1]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h1, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h877, h893, hc12, hc23, hlam, hphi, p897_1]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h877, hlam, p897_1]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h876, h877, h893, h894, h896, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p897_1]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h2, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h2, h876, h894, h896, hc45, hlam, hphi, ht01, ht0b, ht5b, p897_1, u1elo0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p897_1, u1elo0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h2, h876, h894, h896, hc45, hlam, hphi, ht01, ht0b, ht5b, p897_1, u1elo0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h3, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h876, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h891, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [h892, hlam, p897_0]
                                      · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                        linarith only [hlam, p897_0]
                                    · linarith only [h871, h872, h876, h877, h896, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                                  · linarith only [h872, h876, h877, h892, h893, h894, h895, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                                · linarith only [h877, h891, h894, hc23, hc34, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h930 | h930
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h932 | h932
                                    · rcases h1bigk with h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h876, hc25, hlam, hphi, ht0b, ht5b, p933_1, u0elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h872, h876, h930, h932, hc45, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h872, h876, h877, h930, h932, hc45, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        rcases p933_3 (m.d 0 1) (by simp) with h938 | h938
                                        · rcases p933_3 (m.d 1 2) (by simp) with h939 | h939
                                          · linarith only [h0, h939, hlam]
                                          · linarith only [h876, h939, hlam]
                                        · linarith only [h938, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h0, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h872, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h874, hlam, p933_1]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h0, h4, h893, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p933_1]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h1, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h876, h877, hc25, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo3]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h877, hlam, p933_1]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h2, h876, h877, h930, h932, hc45, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h2, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h2, h876, h930, h932, hc45, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h0, h2, h4, h876, h893, h930, h932, hc13, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h2, h876, h930, h932, hc45, hlam, hphi, ht01, ht0b, ht5b, p933_1, u1elo0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h3, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h876, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h891, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [h892, hlam, p933_0]
                                      · obtain ⟨p933_0, p933_1, p933_2, p933_3⟩ := h933c
                                        linarith only [hlam, p933_0]
                                    · linarith only [h0, h4, h876, h893, h930, h932, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h3, h658, h870, h892, h931, hlam]
                                · linarith only [h0, h2, h4, h876, h877, h891, h930, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h2, h871, h877, h891, h892, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h872, h876, h891, hlam]
                      · linarith only [h4, h870, h876, hc12, hc23, hlam, hphi]
                · linarith only [h658, h870, h871, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h970 | h970
                · rcases m.htr 1 2 3 (by decide) (by decide) with h971 | h971
                  · linarith only [h0, h4, h971, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h973 | h973
                    · linarith only [h0, h658, h970, h973, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h975 | h975
                      · linarith only [h0, h870, h975, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h977 | h977
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h978 | h978
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h979 | h979
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h981 | h981
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h982 | h982
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h983 | h983
                                    · linarith only [h1, h977, h983, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h977, h979, h983, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h977, h979, h982, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h1, h4, h978, h981, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h1, h4, h977, h980, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h991 | h991
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h992 | h992
                                    · linarith only [h977, h979, h992, hlam]
                                    · rcases h1bigk with h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        rcases p994_3 (m.d 0 1) (by simp) with h996 | h996
                                        · rcases p994_3 (m.d 1 2) (by simp) with h997 | h997
                                          · linarith only [h997, hlam, p994_0]
                                          · rcases p994_3 (m.d 1 3) (by simp) with h999 | h999
                                            · linarith only [h1, h999, hlam]
                                            · linarith only [h971, h999, hlam]
                                        · linarith only [h996, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h978, hc35, hlam, hphi, ht01, ht0b, ht5b, p994_1, u1elo0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        rcases p994_3 (m.d 0 1) (by simp) with h1004 | h1004
                                        · rcases p994_3 (m.d 1 2) (by simp) with h1005 | h1005
                                          · linarith only [h0, h1005, hlam]
                                          · rcases p994_3 (m.d 1 3) (by simp) with h1007 | h1007
                                            · linarith only [h1, h1007, hlam]
                                            · linarith only [h1007, h977, hlam]
                                        · linarith only [h1004, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        rcases p994_3 (m.d 0 1) (by simp) with h1011 | h1011
                                        · rcases p994_3 (m.d 1 2) (by simp) with h1012 | h1012
                                          · linarith only [h0, h1012, hlam]
                                          · rcases p994_3 (m.d 1 3) (by simp) with h1014 | h1014
                                            · linarith only [h1, h1014, hlam]
                                            · linarith only [h1014, h978, hlam]
                                        · linarith only [h1011, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h0, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h971, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h973, hlam, p994_1]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h975, hlam, p994_1]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h1, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p994_1, u1elo0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h1, h973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p994_1, u1elo0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p994_1, u1elo0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h2, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h970, h979, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p994_1, u0elo3]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h977, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h979, hlam, p994_1]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h3, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p994_1, u1elo0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h978, hlam, p994_0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [h2, h970, h979, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p994_1, u1elo0]
                                      · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                        linarith only [hlam, p994_0]
                                  · linarith only [h658, h970, h991, hlam]
                                · linarith only [h1, h658, h978, h989, h990, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h4, h977, h989, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1041 | h1041
                            · linarith only [h1041, h977, h978, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1043 | h1043
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1044 | h1044
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1045 | h1045
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1046 | h1046
                                    · linarith only [h1, h1041, h1046, h973, h977, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                    · linarith only [h1046, h2, h970, h977, h978, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1045, h658, h970, hlam]
                                · linarith only [h1041, h1043, h1044, h658, h970, h973, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h1043, h4, h977, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1052 | h1052
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1053 | h1053
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1054 | h1054
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1055 | h1055
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1056 | h1056
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1057 | h1057
                                    · rcases h1bigk with h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        rcases p1058_3 (m.d 0 1) (by simp) with h1060 | h1060
                                        · rcases p1058_3 (m.d 1 2) (by simp) with h1061 | h1061
                                          · linarith only [h1061, hlam, p1058_0]
                                          · rcases p1058_3 (m.d 1 3) (by simp) with h1063 | h1063
                                            · linarith only [h1, h1063, hlam]
                                            · linarith only [h1063, h971, hlam]
                                        · linarith only [h1060, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1052, h1057, hc45, hlam, hphi, ht01, ht0b, ht5b, p1058_1, u1elo0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1052, h1057, h977, hc45, hlam, hphi, ht01, ht0b, ht5b, p1058_1, u1elo0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        rcases p1058_3 (m.d 0 1) (by simp) with h1069 | h1069
                                        · rcases p1058_3 (m.d 1 2) (by simp) with h1070 | h1070
                                          · linarith only [h0, h1070, hlam]
                                          · rcases p1058_3 (m.d 1 3) (by simp) with h1072 | h1072
                                            · linarith only [h1, h1072, hlam]
                                            · linarith only [h1052, h1072, hlam]
                                        · linarith only [h1069, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h0, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h971, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h973, hlam, p1058_1]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h975, hlam, p1058_1]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1054, h977, hc12, hc23, hlam, hphi, p1058_1]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h977, hlam, p1058_1]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1054, h977, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1058_1]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h2, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1058_1, u1elo0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1058_1, u1elo0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h2, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1058_1, u1elo0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h3, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1058_1, u1elo0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1052, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [h1053, hlam, p1058_0]
                                      · obtain ⟨p1058_0, p1058_1, p1058_2, p1058_3⟩ := h1058c
                                        linarith only [hlam, p1058_0]
                                    · linarith only [h1057, h2, h970, h977, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1053, h1056, h2, h658, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h1052, h1055, h977, hc23, hc34, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1099 | h1099
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1100 | h1100
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1101 | h1101
                                    · rcases h1bigk with h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        rcases p1102_3 (m.d 0 1) (by simp) with h1104 | h1104
                                        · rcases p1102_3 (m.d 1 2) (by simp) with h1105 | h1105
                                          · linarith only [h1105, hlam, p1102_0]
                                          · rcases p1102_3 (m.d 1 3) (by simp) with h1107 | h1107
                                            · linarith only [h1, h1107, hlam]
                                            · linarith only [h1107, h971, hlam]
                                        · linarith only [h1104, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h1052, hc35, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h1052, h1101, h977, hc45, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        rcases p1102_3 (m.d 0 1) (by simp) with h1113 | h1113
                                        · rcases p1102_3 (m.d 1 2) (by simp) with h1114 | h1114
                                          · linarith only [h0, h1114, hlam]
                                          · rcases p1102_3 (m.d 1 3) (by simp) with h1116 | h1116
                                            · linarith only [h1, h1116, hlam]
                                            · linarith only [h1052, h1116, hlam]
                                        · linarith only [h1113, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h0, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h971, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h973, hlam, p1102_1]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h975, hlam, p1102_1]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h1, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h977, hlam, p1102_1]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h2, h977, hc15, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h2, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h2, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h3, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1102_1, u1elo0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h1052, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [h1053, hlam, p1102_0]
                                      · obtain ⟨p1102_0, p1102_1, p1102_2, p1102_3⟩ := h1102c
                                        linarith only [hlam, p1102_0]
                                    · linarith only [h0, h1054, h1101, h2, h658, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1053, h1100, h2, h658, hlam]
                                · linarith only [h1, h1052, h1099, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h1052, h1053, h970, h977, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1144 | h1144
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1145 | h1145
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1146 | h1146
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1147 | h1147
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1148 | h1148
                                    · rcases h1bigk with h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1151 | h1151
                                        · rcases p1149_3 (m.d 1 2) (by simp) with h1152 | h1152
                                          · linarith only [h1152, hlam, p1149_0]
                                          · rcases p1149_3 (m.d 1 3) (by simp) with h1154 | h1154
                                            · linarith only [h1, h1154, hlam]
                                            · linarith only [h1154, h971, hlam]
                                        · linarith only [h1151, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1158 | h1158
                                        · rcases p1149_3 (m.d 1 2) (by simp) with h1159 | h1159
                                          · linarith only [h0, h1159, hlam]
                                          · rcases p1149_3 (m.d 1 3) (by simp) with h1161 | h1161
                                            · linarith only [h1161, hlam, p1149_0]
                                            · rcases p1149_3 (m.d 1 4) (by simp) with h1163 | h1163
                                              · linarith only [h1163, h2, hlam]
                                              · linarith only [h1163, h977, hlam]
                                        · linarith only [h1158, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h1144, hc45, hlam, hphi, ht01, ht0b, ht5b, p1149_1, u1elo0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1168 | h1168
                                        · rcases p1149_3 (m.d 1 2) (by simp) with h1169 | h1169
                                          · linarith only [h0, h1169, hlam]
                                          · rcases p1149_3 (m.d 1 3) (by simp) with h1171 | h1171
                                            · linarith only [h1, h1171, hlam]
                                            · rcases p1149_3 (m.d 1 4) (by simp) with h1173 | h1173
                                              · linarith only [h1173, h2, hlam]
                                              · linarith only [h1144, h1173, hlam]
                                        · linarith only [h1168, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h0, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h971, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h973, hlam, p1149_1]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h975, hlam, p1149_1]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h1, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h1052, h1148, hc12, hc34, hlam, hphi, ht23, p1149_1]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h977, hlam, p1149_1]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h1052, hlam, p1149_1]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h2, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1149_1, u1elo0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1149_1, u1elo0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1149_1, u1elo0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h3, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1149_1, u1elo0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h3, h971, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1149_1, u1elo0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [h1144, hlam, p1149_0]
                                      · obtain ⟨p1149_0, p1149_1, p1149_2, p1149_3⟩ := h1149c
                                        linarith only [hlam, p1149_0]
                                    · linarith only [h1148, h2, h970, h971, h977, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1144, h1147, h2, h658, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h1145, h1146, h971, h977, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1200 | h1200
                                · linarith only [h1052, h1145, h1200, h971, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1203 | h1203
                                    · rcases h1bigk with h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        rcases p1204_3 (m.d 0 1) (by simp) with h1206 | h1206
                                        · rcases p1204_3 (m.d 1 2) (by simp) with h1207 | h1207
                                          · linarith only [h1207, hlam, p1204_0]
                                          · rcases p1204_3 (m.d 1 3) (by simp) with h1209 | h1209
                                            · linarith only [h1, h1209, hlam]
                                            · linarith only [h1209, h971, hlam]
                                        · linarith only [h1206, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        rcases p1204_3 (m.d 0 1) (by simp) with h1213 | h1213
                                        · rcases p1204_3 (m.d 1 2) (by simp) with h1214 | h1214
                                          · linarith only [h0, h1214, hlam]
                                          · rcases p1204_3 (m.d 1 3) (by simp) with h1216 | h1216
                                            · linarith only [h1216, hlam, p1204_0]
                                            · rcases p1204_3 (m.d 1 4) (by simp) with h1218 | h1218
                                              · linarith only [h1218, h2, hlam]
                                              · linarith only [h1218, h977, hlam]
                                        · linarith only [h1213, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h1144, hc45, hlam, hphi, ht01, ht0b, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        rcases p1204_3 (m.d 0 1) (by simp) with h1223 | h1223
                                        · rcases p1204_3 (m.d 1 2) (by simp) with h1224 | h1224
                                          · linarith only [h0, h1224, hlam]
                                          · rcases p1204_3 (m.d 1 3) (by simp) with h1226 | h1226
                                            · linarith only [h1, h1226, hlam]
                                            · rcases p1204_3 (m.d 1 4) (by simp) with h1228 | h1228
                                              · linarith only [h1228, h2, hlam]
                                              · linarith only [h1144, h1228, hlam]
                                        · linarith only [h1223, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h0, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h971, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h973, hlam, p1204_1]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h975, hlam, p1204_1]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h1, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h977, hlam, p1204_1]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h1052, hlam, p1204_1]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h2, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h3, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h3, h971, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1204_1, u1elo0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [h1144, hlam, p1204_0]
                                      · obtain ⟨p1204_0, p1204_1, p1204_2, p1204_3⟩ := h1204c
                                        linarith only [hlam, p1204_0]
                                    · linarith only [h1203, h970, h971, h977, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                  · linarith only [h1144, h1202, h2, h658, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1254 | h1254
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1255 | h1255
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1256 | h1256
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
                                    · linarith only [h1144, h1254, h1257, h971, h977, hc12, hc23, hlam, hphi]
                                    · linarith only [h1257, h2, h970, h971, h977, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1256, h658, h970, hlam]
                                · linarith only [h1254, h1255, h971, h977, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1262 | h1262
                                · linarith only [h1052, h1254, h1262, h971, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1264 | h1264
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1265 | h1265
                                    · rcases h1bigk with h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        rcases p1266_3 (m.d 0 1) (by simp) with h1268 | h1268
                                        · rcases p1266_3 (m.d 1 2) (by simp) with h1269 | h1269
                                          · linarith only [h1269, hlam, p1266_0]
                                          · rcases p1266_3 (m.d 1 3) (by simp) with h1271 | h1271
                                            · linarith only [h1, h1271, hlam]
                                            · linarith only [h1271, h971, hlam]
                                        · linarith only [h1268, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        rcases p1266_3 (m.d 0 1) (by simp) with h1275 | h1275
                                        · rcases p1266_3 (m.d 1 2) (by simp) with h1276 | h1276
                                          · linarith only [h0, h1276, hlam]
                                          · rcases p1266_3 (m.d 1 3) (by simp) with h1278 | h1278
                                            · linarith only [h1278, hlam, p1266_0]
                                            · rcases p1266_3 (m.d 1 4) (by simp) with h1280 | h1280
                                              · linarith only [h1280, h2, hlam]
                                              · linarith only [h1280, h977, hlam]
                                        · linarith only [h1275, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        rcases p1266_3 (m.d 0 1) (by simp) with h1284 | h1284
                                        · rcases p1266_3 (m.d 1 2) (by simp) with h1285 | h1285
                                          · linarith only [h0, h1285, hlam]
                                          · rcases p1266_3 (m.d 1 3) (by simp) with h1287 | h1287
                                            · linarith only [h1, h1287, hlam]
                                            · rcases p1266_3 (m.d 1 4) (by simp) with h1289 | h1289
                                              · linarith only [h1289, hlam, p1266_0]
                                              · rcases p1266_3 (m.d 1 5) (by simp) with h1291 | h1291
                                                · linarith only [h1291, h3, hlam]
                                                · linarith only [h1144, h1291, hlam]
                                        · linarith only [h1284, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        rcases p1266_3 (m.d 0 1) (by simp) with h1295 | h1295
                                        · rcases p1266_3 (m.d 1 2) (by simp) with h1296 | h1296
                                          · linarith only [h0, h1296, hlam]
                                          · rcases p1266_3 (m.d 1 3) (by simp) with h1298 | h1298
                                            · linarith only [h1, h1298, hlam]
                                            · rcases p1266_3 (m.d 1 4) (by simp) with h1300 | h1300
                                              · linarith only [h1300, h2, hlam]
                                              · rcases p1266_3 (m.d 1 5) (by simp) with h1302 | h1302
                                                · linarith only [h1302, hlam, p1266_0]
                                                · rcases h2bigk with h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h1262, h1265, h4, hc12, hc34, hlam, hphi, ht23, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h4, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h658, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h870, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h0, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h971, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h973, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h975, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h1262, h1265, hc02, hc34, hlam, hphi, ht23, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h1262, h1265, hc12, hc34, hlam, hphi, ht23, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h1254, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h1262, hlam, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    rcases p1304_3 (m.d 0 2) (by simp) with h1320 | h1320
                                                    · linarith only [h1320, hlam, p1304_0]
                                                    · rcases p1304_3 (m.d 1 2) (by simp) with h1322 | h1322
                                                      · linarith only [h1322, h973, hlam]
                                                      · rcases p1304_3 (m.d 2 3) (by simp) with h1324 | h1324
                                                        · linarith only [h1254, h1324, hlam]
                                                        · linarith only [h1324, h4, hlam]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    rcases p1304_3 (m.d 0 2) (by simp) with h1327 | h1327
                                                    · linarith only [h1327, h658, hlam]
                                                    · linarith only [h0, h1327, hlam]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h0, h4, hc12, hc24, hlam, hphi, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h0, h1254, h870, hc12, hc34, hlam, hphi, ht23, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    rcases p1304_3 (m.d 0 2) (by simp) with h1333 | h1333
                                                    · linarith only [h1333, hlam, p1304_0]
                                                    · rcases p1304_3 (m.d 1 2) (by simp) with h1335 | h1335
                                                      · linarith only [h1335, h975, hlam]
                                                      · rcases p1304_3 (m.d 2 3) (by simp) with h1337 | h1337
                                                        · linarith only [h1262, h1337, hlam]
                                                        · linarith only [h1337, h4, hlam]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    rcases p1304_3 (m.d 0 2) (by simp) with h1340 | h1340
                                                    · linarith only [h1340, h870, hlam]
                                                    · linarith only [h0, h1340, hlam]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h0, h4, hc12, hc25, hlam, hphi, p1304_1]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [h1264, hlam, p1304_0]
                                                  · obtain ⟨p1304_0, p1304_1, p1304_2, p1304_3⟩ := h1304c
                                                    linarith only [hlam, p1304_0]
                                        · linarith only [h1295, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h0, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h971, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h973, hlam, p1266_1]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h975, hlam, p1266_1]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h1, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1266_1, u1elo0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h977, hlam, p1266_1]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h1052, hlam, p1266_1]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h2, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1266_1, u1elo0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1266_1, u1elo0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h1144, hlam, p1266_1]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h3, hlam, p1266_0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1266_1, u1elo0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h3, h971, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1266_1, u1elo0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [h1144, h2, h970, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1266_1, u1elo0]
                                      · obtain ⟨p1266_0, p1266_1, p1266_2, p1266_3⟩ := h1266c
                                        linarith only [hlam, p1266_0]
                                    · linarith only [h0, h1254, h1265, h2, h658, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h1264, h658, h970, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1369 | h1369
                  · linarith only [h0, h1369, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1371 | h1371
                    · linarith only [h0, h1371, h658, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1373 | h1373
                      · linarith only [h1, h1369, h1373, h870, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1375 | h1375
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1376 | h1376
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1377 | h1377
                            · linarith only [h1377, h2, h970, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1379 | h1379
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1380 | h1380
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1381 | h1381
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1382 | h1382
                                    · linarith only [h0, h1375, h1382, h2, h658, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                    · rcases h1bigk with h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        rcases p1384_3 (m.d 0 1) (by simp) with h1386 | h1386
                                        · rcases p1384_3 (m.d 1 2) (by simp) with h1387 | h1387
                                          · linarith only [h1387, hlam, p1384_0]
                                          · rcases p1384_3 (m.d 1 3) (by simp) with h1389 | h1389
                                            · linarith only [h1, h1389, hlam]
                                            · linarith only [h1369, h1389, hlam]
                                        · linarith only [h1386, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1375, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        rcases p1384_3 (m.d 0 1) (by simp) with h1394 | h1394
                                        · rcases p1384_3 (m.d 1 2) (by simp) with h1395 | h1395
                                          · linarith only [h0, h1395, hlam]
                                          · rcases p1384_3 (m.d 1 3) (by simp) with h1397 | h1397
                                            · linarith only [h1, h1397, hlam]
                                            · linarith only [h1375, h1397, hlam]
                                        · linarith only [h1394, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        rcases p1384_3 (m.d 0 1) (by simp) with h1401 | h1401
                                        · rcases p1384_3 (m.d 1 2) (by simp) with h1402 | h1402
                                          · linarith only [h0, h1402, hlam]
                                          · rcases p1384_3 (m.d 1 3) (by simp) with h1404 | h1404
                                            · linarith only [h1, h1404, hlam]
                                            · linarith only [h1376, h1404, hlam]
                                        · linarith only [h1401, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h0, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1369, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1371, hlam, p1384_1]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1373, hlam, p1384_1]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h2, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1375, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1377, hlam, p1384_1]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h3, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1376, hlam, p1384_0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [h1, h1376, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1384_1, u1elo0]
                                      · obtain ⟨p1384_0, p1384_1, p1384_2, p1384_3⟩ := h1384c
                                        linarith only [hlam, p1384_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1428 | h1428
                                    · linarith only [h0, h1381, h1428, h658, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        rcases p1430_3 (m.d 0 1) (by simp) with h1432 | h1432
                                        · rcases p1430_3 (m.d 1 2) (by simp) with h1433 | h1433
                                          · linarith only [h1433, hlam, p1430_0]
                                          · rcases p1430_3 (m.d 1 3) (by simp) with h1435 | h1435
                                            · linarith only [h1, h1435, hlam]
                                            · linarith only [h1369, h1435, hlam]
                                        · linarith only [h1432, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1375, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        rcases p1430_3 (m.d 0 1) (by simp) with h1440 | h1440
                                        · rcases p1430_3 (m.d 1 2) (by simp) with h1441 | h1441
                                          · linarith only [h0, h1441, hlam]
                                          · rcases p1430_3 (m.d 1 3) (by simp) with h1443 | h1443
                                            · linarith only [h1, h1443, hlam]
                                            · linarith only [h1375, h1443, hlam]
                                        · linarith only [h1440, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        rcases p1430_3 (m.d 0 1) (by simp) with h1447 | h1447
                                        · rcases p1430_3 (m.d 1 2) (by simp) with h1448 | h1448
                                          · linarith only [h0, h1448, hlam]
                                          · rcases p1430_3 (m.d 1 3) (by simp) with h1450 | h1450
                                            · linarith only [h1, h1450, hlam]
                                            · linarith only [h1376, h1450, hlam]
                                        · linarith only [h1447, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h0, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1369, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1371, hlam, p1430_1]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1373, hlam, p1430_1]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1, h1371, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h2, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1375, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1377, hlam, p1430_1]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h3, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1376, hlam, p1430_0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [h1, h1376, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1430_1, u1elo0]
                                      · obtain ⟨p1430_0, p1430_1, p1430_2, p1430_3⟩ := h1430c
                                        linarith only [hlam, p1430_0]
                                · linarith only [h1, h1376, h1380, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h1, h1375, h1379, h4, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1476 | h1476
                            · linarith only [h1476, h2, h970, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1478 | h1478
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1479 | h1479
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1480 | h1480
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1481 | h1481
                                    · linarith only [h1375, h1376, h1479, h1481, h970, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · rcases h1bigk with h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        rcases p1483_3 (m.d 0 1) (by simp) with h1485 | h1485
                                        · rcases p1483_3 (m.d 1 2) (by simp) with h1486 | h1486
                                          · linarith only [h1486, hlam, p1483_0]
                                          · rcases p1483_3 (m.d 1 3) (by simp) with h1488 | h1488
                                            · linarith only [h1, h1488, hlam]
                                            · linarith only [h1369, h1488, hlam]
                                        · linarith only [h1485, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1375, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1, u1elo0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        rcases p1483_3 (m.d 0 1) (by simp) with h1493 | h1493
                                        · rcases p1483_3 (m.d 1 2) (by simp) with h1494 | h1494
                                          · linarith only [h0, h1494, hlam]
                                          · rcases p1483_3 (m.d 1 3) (by simp) with h1496 | h1496
                                            · linarith only [h1, h1496, hlam]
                                            · linarith only [h1375, h1496, hlam]
                                        · linarith only [h1493, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1375, h1376, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1, u1elo0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h0, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1369, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1371, hlam, p1483_1]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1373, hlam, p1483_1]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1376, h1478, h1480, h1481, hc12, hc23, hlam, hphi, p1483_1]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1376, h1478, h1480, h1481, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1483_1]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1376, hlam, p1483_1]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h2, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1483_1, u1elo0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1375, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1476, hlam, p1483_1]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h3, hlam, p1483_0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1375, h1376, h1478, h1480, h1481, h3, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1, u1elo0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h1375, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1, u1elo0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1, u1elo0]
                                      · obtain ⟨p1483_0, p1483_1, p1483_2, p1483_3⟩ := h1483c
                                        linarith only [hlam, p1483_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1521 | h1521
                                    · linarith only [h1, h1375, h1480, h1521, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h1bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        rcases p1523_3 (m.d 0 1) (by simp) with h1525 | h1525
                                        · rcases p1523_3 (m.d 1 2) (by simp) with h1526 | h1526
                                          · linarith only [h1526, hlam, p1523_0]
                                          · rcases p1523_3 (m.d 1 3) (by simp) with h1528 | h1528
                                            · linarith only [h1, h1528, hlam]
                                            · linarith only [h1369, h1528, hlam]
                                        · linarith only [h1525, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1375, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        rcases p1523_3 (m.d 0 1) (by simp) with h1533 | h1533
                                        · rcases p1523_3 (m.d 1 2) (by simp) with h1534 | h1534
                                          · linarith only [h0, h1534, hlam]
                                          · rcases p1523_3 (m.d 1 3) (by simp) with h1536 | h1536
                                            · linarith only [h1, h1536, hlam]
                                            · linarith only [h1375, h1536, hlam]
                                        · linarith only [h1533, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1375, h1376, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h0, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1369, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1371, hlam, p1523_1]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1373, hlam, p1523_1]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1376, hlam, p1523_1]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h2, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1375, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1476, hlam, p1523_1]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h3, hlam, p1523_0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [h1371, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1523_1, u1elo0]
                                      · obtain ⟨p1523_0, p1523_1, p1523_2, p1523_3⟩ := h1523c
                                        linarith only [hlam, p1523_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1561 | h1561
                                  · linarith only [h1371, h1478, h1479, h1561, h2, h970, hc12, hc35, hlam, hphi, ht23]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1563 | h1563
                                    · linarith only [h1, h1375, h1561, h1563, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h1bigk with h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        rcases p1565_3 (m.d 0 1) (by simp) with h1567 | h1567
                                        · rcases p1565_3 (m.d 1 2) (by simp) with h1568 | h1568
                                          · linarith only [h1568, hlam, p1565_0]
                                          · rcases p1565_3 (m.d 1 3) (by simp) with h1570 | h1570
                                            · linarith only [h1, h1570, hlam]
                                            · linarith only [h1369, h1570, hlam]
                                        · linarith only [h1567, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1375, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        rcases p1565_3 (m.d 0 1) (by simp) with h1575 | h1575
                                        · rcases p1565_3 (m.d 1 2) (by simp) with h1576 | h1576
                                          · linarith only [h0, h1576, hlam]
                                          · rcases p1565_3 (m.d 1 3) (by simp) with h1578 | h1578
                                            · linarith only [h1, h1578, hlam]
                                            · linarith only [h1375, h1578, hlam]
                                        · linarith only [h1575, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1375, h1376, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h0, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1369, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1371, hlam, p1565_1]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1373, hlam, p1565_1]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1, h1371, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1376, hlam, p1565_1]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h2, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1375, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1476, hlam, p1565_1]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h3, hlam, p1565_0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [h1371, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u1elo0]
                                      · obtain ⟨p1565_0, p1565_1, p1565_2, p1565_3⟩ := h1565c
                                        linarith only [hlam, p1565_0]
                              · linarith only [h1, h1375, h1478, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1604 | h1604
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1605 | h1605
                            · linarith only [h1605, h2, h970, hlam]
                            · linarith only [h1375, h1604, h1605, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1608 | h1608
                            · linarith only [h1608, h2, h970, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1610 | h1610
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1611 | h1611
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1612 | h1612
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1613 | h1613
                                    · linarith only [h0, h1610, h1613, h658, h970, hc12, hc23, hlam, hphi]
                                    · linarith only [h1369, h1375, h1610, h1612, h1613, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1616 | h1616
                                    · linarith only [h1610, h1612, h1616, hlam]
                                    · rcases h1bigk with h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        rcases p1618_3 (m.d 0 1) (by simp) with h1620 | h1620
                                        · rcases p1618_3 (m.d 1 2) (by simp) with h1621 | h1621
                                          · linarith only [h1621, hlam, p1618_0]
                                          · rcases p1618_3 (m.d 1 3) (by simp) with h1623 | h1623
                                            · linarith only [h1, h1623, hlam]
                                            · linarith only [h1369, h1623, hlam]
                                        · linarith only [h1620, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        rcases p1618_3 (m.d 0 1) (by simp) with h1627 | h1627
                                        · rcases p1618_3 (m.d 1 2) (by simp) with h1628 | h1628
                                          · linarith only [h0, h1628, hlam]
                                          · rcases p1618_3 (m.d 1 3) (by simp) with h1630 | h1630
                                            · linarith only [h1630, hlam, p1618_0]
                                            · rcases p1618_3 (m.d 1 4) (by simp) with h1632 | h1632
                                              · linarith only [h1632, h2, hlam]
                                              · linarith only [h1375, h1632, hlam]
                                        · linarith only [h1627, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        rcases p1618_3 (m.d 0 1) (by simp) with h1636 | h1636
                                        · rcases p1618_3 (m.d 1 2) (by simp) with h1637 | h1637
                                          · linarith only [h0, h1637, hlam]
                                          · rcases p1618_3 (m.d 1 3) (by simp) with h1639 | h1639
                                            · linarith only [h1, h1639, hlam]
                                            · rcases p1618_3 (m.d 1 4) (by simp) with h1641 | h1641
                                              · linarith only [h1641, hlam, p1618_0]
                                              · rcases p1618_3 (m.d 1 5) (by simp) with h1643 | h1643
                                                · linarith only [h1643, h3, hlam]
                                                · linarith only [h1608, h1643, hlam]
                                        · linarith only [h1636, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        rcases p1618_3 (m.d 0 1) (by simp) with h1647 | h1647
                                        · rcases p1618_3 (m.d 1 2) (by simp) with h1648 | h1648
                                          · linarith only [h0, h1648, hlam]
                                          · rcases p1618_3 (m.d 1 3) (by simp) with h1650 | h1650
                                            · linarith only [h1, h1650, hlam]
                                            · rcases p1618_3 (m.d 1 4) (by simp) with h1652 | h1652
                                              · linarith only [h1652, h2, hlam]
                                              · rcases p1618_3 (m.d 1 5) (by simp) with h1654 | h1654
                                                · linarith only [h1654, hlam, p1618_0]
                                                · rcases h2bigk with h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h4, hc12, hc23, hlam, hphi, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h4, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h658, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h870, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h0, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1369, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1371, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1373, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    rcases p1656_3 (m.d 0 2) (by simp) with h1667 | h1667
                                                    · linarith only [h1667, hlam, p1656_0]
                                                    · rcases p1656_3 (m.d 1 2) (by simp) with h1669 | h1669
                                                      · linarith only [h1369, h1669, hlam]
                                                      · rcases p1656_3 (m.d 2 3) (by simp) with h1671 | h1671
                                                        · rcases p1656_3 (m.d 2 4) (by simp) with h1672 | h1672
                                                          · linarith only [h1610, h1672, hlam]
                                                          · linarith only [h1672, h658, hlam]
                                                        · linarith only [h1671, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    rcases p1656_3 (m.d 0 2) (by simp) with h1676 | h1676
                                                    · linarith only [h1676, h4, hlam]
                                                    · linarith only [h0, h1676, hlam]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1369, h1375, h1610, hc12, hc23, hlam, hphi, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h870, hc02, hc23, hlam, hphi, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h0, h1612, hc12, hc45, hlam, hphi, ht23, ht34, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1612, hc12, hc45, hlam, hphi, ht23, ht34, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1610, hlam, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1612, hlam, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    rcases p1656_3 (m.d 0 2) (by simp) with h1687 | h1687
                                                    · linarith only [h1687, hlam, p1656_0]
                                                    · rcases p1656_3 (m.d 1 2) (by simp) with h1689 | h1689
                                                      · linarith only [h1373, h1689, hlam]
                                                      · rcases p1656_3 (m.d 2 3) (by simp) with h1691 | h1691
                                                        · rcases p1656_3 (m.d 2 4) (by simp) with h1692 | h1692
                                                          · linarith only [h1612, h1692, hlam]
                                                          · linarith only [h1692, h658, hlam]
                                                        · linarith only [h1691, h4, hlam]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    rcases p1656_3 (m.d 0 2) (by simp) with h1696 | h1696
                                                    · linarith only [h1696, h870, hlam]
                                                    · linarith only [h0, h1696, hlam]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h1611, hlam, p1656_0]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [h0, h658, hc12, hc25, hlam, hphi, p1656_1]
                                                  · obtain ⟨p1656_0, p1656_1, p1656_2, p1656_3⟩ := h1656c
                                                    linarith only [hlam, p1656_0]
                                        · linarith only [h1647, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h0, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1369, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1371, hlam, p1618_1]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1373, hlam, p1618_1]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1375, hc12, hc34, hlam, hphi, ht23, p1618_1]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1375, hlam, p1618_1]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1604, hlam, p1618_1]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h2, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1608, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1618_1, u1elo0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1608, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1618_1, u1elo0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1608, hlam, p1618_1]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h3, hlam, p1618_0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1618_1, u1elo0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h1369, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1618_1, u1elo0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1618_1, u1elo0]
                                      · obtain ⟨p1618_0, p1618_1, p1618_2, p1618_3⟩ := h1618c
                                        linarith only [hlam, p1618_0]
                                · linarith only [h1369, h1375, h1610, h1611, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1724 | h1724
                                · linarith only [h1369, h1604, h1610, h1724, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1726 | h1726
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1727 | h1727
                                    · rcases h1bigk with h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        rcases p1728_3 (m.d 0 1) (by simp) with h1730 | h1730
                                        · rcases p1728_3 (m.d 1 2) (by simp) with h1731 | h1731
                                          · linarith only [h1731, hlam, p1728_0]
                                          · rcases p1728_3 (m.d 1 3) (by simp) with h1733 | h1733
                                            · linarith only [h1, h1733, hlam]
                                            · linarith only [h1369, h1733, hlam]
                                        · linarith only [h1730, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        rcases p1728_3 (m.d 0 1) (by simp) with h1737 | h1737
                                        · rcases p1728_3 (m.d 1 2) (by simp) with h1738 | h1738
                                          · linarith only [h0, h1738, hlam]
                                          · rcases p1728_3 (m.d 1 3) (by simp) with h1740 | h1740
                                            · linarith only [h1740, hlam, p1728_0]
                                            · rcases p1728_3 (m.d 1 4) (by simp) with h1742 | h1742
                                              · linarith only [h1742, h2, hlam]
                                              · linarith only [h1375, h1742, hlam]
                                        · linarith only [h1737, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        rcases p1728_3 (m.d 0 1) (by simp) with h1746 | h1746
                                        · rcases p1728_3 (m.d 1 2) (by simp) with h1747 | h1747
                                          · linarith only [h0, h1747, hlam]
                                          · rcases p1728_3 (m.d 1 3) (by simp) with h1749 | h1749
                                            · linarith only [h1, h1749, hlam]
                                            · rcases p1728_3 (m.d 1 4) (by simp) with h1751 | h1751
                                              · linarith only [h1751, hlam, p1728_0]
                                              · rcases p1728_3 (m.d 1 5) (by simp) with h1753 | h1753
                                                · linarith only [h1753, h3, hlam]
                                                · linarith only [h1608, h1753, hlam]
                                        · linarith only [h1746, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        rcases p1728_3 (m.d 0 1) (by simp) with h1757 | h1757
                                        · rcases p1728_3 (m.d 1 2) (by simp) with h1758 | h1758
                                          · linarith only [h0, h1758, hlam]
                                          · rcases p1728_3 (m.d 1 3) (by simp) with h1760 | h1760
                                            · linarith only [h1, h1760, hlam]
                                            · rcases p1728_3 (m.d 1 4) (by simp) with h1762 | h1762
                                              · linarith only [h1762, h2, hlam]
                                              · rcases p1728_3 (m.d 1 5) (by simp) with h1764 | h1764
                                                · linarith only [h1764, hlam, p1728_0]
                                                · rcases h2bigk with h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1724, h1727, h4, hc12, hc34, hlam, hphi, ht23, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h4, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h658, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h870, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h0, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1369, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1371, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1373, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1724, h1727, hc02, hc34, hlam, hphi, ht23, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1724, h1727, hc12, hc34, hlam, hphi, ht23, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1610, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1724, hlam, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    rcases p1766_3 (m.d 0 2) (by simp) with h1782 | h1782
                                                    · linarith only [h1782, hlam, p1766_0]
                                                    · rcases p1766_3 (m.d 1 2) (by simp) with h1784 | h1784
                                                      · linarith only [h1371, h1784, hlam]
                                                      · rcases p1766_3 (m.d 2 3) (by simp) with h1786 | h1786
                                                        · linarith only [h1610, h1786, hlam]
                                                        · linarith only [h1786, h4, hlam]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    rcases p1766_3 (m.d 0 2) (by simp) with h1789 | h1789
                                                    · linarith only [h1789, h658, hlam]
                                                    · linarith only [h0, h1789, hlam]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h0, h4, hc12, hc24, hlam, hphi, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h0, h870, hc12, hc24, hlam, hphi, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    rcases p1766_3 (m.d 0 2) (by simp) with h1795 | h1795
                                                    · linarith only [h1795, hlam, p1766_0]
                                                    · rcases p1766_3 (m.d 1 2) (by simp) with h1797 | h1797
                                                      · linarith only [h1373, h1797, hlam]
                                                      · rcases p1766_3 (m.d 2 3) (by simp) with h1799 | h1799
                                                        · linarith only [h1724, h1799, hlam]
                                                        · linarith only [h1799, h4, hlam]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    rcases p1766_3 (m.d 0 2) (by simp) with h1802 | h1802
                                                    · linarith only [h1802, h870, hlam]
                                                    · linarith only [h0, h1802, hlam]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h0, h4, hc12, hc25, hlam, hphi, p1766_1]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [h1726, hlam, p1766_0]
                                                  · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                                    linarith only [hlam, p1766_0]
                                        · linarith only [h1757, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h0, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1369, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1371, hlam, p1728_1]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1373, hlam, p1728_1]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1375, h2, h970, hc12, hc45, hlam, hphi, ht23, ht34, p1728_1]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1375, hlam, p1728_1]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1604, hlam, p1728_1]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h2, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1728_1, u1elo0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1728_1, u1elo0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1608, hlam, p1728_1]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h3, hlam, p1728_0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1728_1, u1elo0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h1369, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1728_1, u1elo0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1728_1, u1elo0]
                                      · obtain ⟨p1728_0, p1728_1, p1728_2, p1728_3⟩ := h1728c
                                        linarith only [hlam, p1728_0]
                                    · linarith only [h1610, h1726, h1727, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1830 | h1830
                                    · linarith only [h0, h1610, h1726, h1830, h4, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h1610, h1830, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1833 | h1833
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1834 | h1834
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1835 | h1835
              · linarith only [h0, h1835, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1837 | h1837
                · linarith only [h0, h1834, h1837, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1839 | h1839
                  · linarith only [h0, h1839, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h0, h1833, h1839, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1842 | h1842
              · linarith only [h1834, h1842, h2, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1844 | h1844
                · linarith only [h1844, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1846 | h1846
                  · linarith only [h0, h1846, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h1833, h1834, h1846, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1849 | h1849
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1850 | h1850
              · linarith only [h0, h1850, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1852 | h1852
                · linarith only [h1, h1833, h1849, h1852, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1854 | h1854
                  · linarith only [h1833, h1849, h1854, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1856 | h1856
                    · linarith only [h1, h1854, h1856, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · linarith only [h1833, h1849, h1856, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1859 | h1859
              · linarith only [h1, h1833, h1859, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1861 | h1861
                · linarith only [h1861, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1863 | h1863
                  · linarith only [h0, h1833, h1863, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1865 | h1865
                    · linarith only [h0, h1849, h1865, h3, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1867 | h1867
                      · linarith only [h1, h1859, h1863, h1867, h3, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1869 | h1869
                        · linarith only [h1, h1869, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1871 | h1871
                          · linarith only [h1869, h1871, h2, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1873 | h1873
                            · linarith only [h1861, h1873, h2, h3, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1876 | h1876
                                · linarith only [h1863, h1869, h1871, h1876, h2, h3, hc12, hc23, hlam, hphi]
                                · linarith only [h1863, h1869, h1875, h1876, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1879 | h1879
                                · linarith only [h1863, h1871, h1875, h1879, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1881 | h1881
                                  · linarith only [h1863, h1869, h1873, h1881, h2, h3, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1883 | h1883
                                    · linarith only [h0, h1833, h1875, h1881, h1883, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h1833, h1875, h1883, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1886 | h1886
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1887 | h1887
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1888 | h1888
            · linarith only [h0, h1888, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1890 | h1890
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1891 | h1891
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1892 | h1892
                  · linarith only [h0, h1892, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h1887, h1892, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h1890, h1891, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1896 | h1896
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1897 | h1897
                  · linarith only [h0, h1897, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h1886, h1887, h1890, h1897, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h1886, h1896, h2, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1901 | h1901
            · linarith only [h0, h1901, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1903 | h1903
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1904 | h1904
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1905 | h1905
                  · linarith only [h1887, h1903, h1905, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1907 | h1907
                    · linarith only [h1901, h1903, h1907, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1909 | h1909
                      · linarith only [h1, h1905, h1909, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · linarith only [h1887, h1903, h1909, hc12, hc23, hlam, hphi]
                · linarith only [h1, h1887, h1903, h1904, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1913 | h1913
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1914 | h1914
                  · linarith only [h0, h1914, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1916 | h1916
                    · linarith only [h1, h1901, h1914, h1916, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1918 | h1918
                      · linarith only [h0, h1903, h1918, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1920 | h1920
                        · linarith only [h1, h1920, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1922 | h1922
                          · linarith only [h1, h1922, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1924 | h1924
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1925 | h1925
                              · linarith only [h0, h1920, h1925, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1927 | h1927
                                · linarith only [h1914, h1922, h1925, h1927, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1929 | h1929
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1930 | h1930
                                    · rcases h1bigk with h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1914, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h2, hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1914, h1922, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h0, hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1914, hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1916, hlam, p1931_1]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1918, hlam, p1931_1]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1, hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1920, hlam, p1931_1]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1922, hlam, p1931_1]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [hc01, hlam, hphi, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        rcases p1931_3 (m.d 0 1) (by simp) with h1948 | h1948
                                        · linarith only [h1948, h2, hlam]
                                        · linarith only [h0, h1948, hlam]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        rcases p1931_3 (m.d 0 1) (by simp) with h1951 | h1951
                                        · linarith only [h1951, h2, hlam]
                                        · linarith only [h1, h1951, hlam]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        rcases p1931_3 (m.d 0 1) (by simp) with h1955 | h1955
                                        · linarith only [h1955, h2, hlam]
                                        · linarith only [h1886, h1955, hlam]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1886, hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1886, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1886, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1931_1, u1elo3]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [h1924, hlam, p1931_0]
                                      · obtain ⟨p1931_0, p1931_1, p1931_2, p1931_3⟩ := h1931c
                                        linarith only [hlam, p1931_0]
                                    · linarith only [h1886, h1924, h1930, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                                  · linarith only [h1886, h1916, h1924, h1929, h2, hlam]
                            · linarith only [h0, h1924, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1886, h1913, h2, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1967 | h1967
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1968 | h1968
            · linarith only [h0, h1968, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1970 | h1970
              · linarith only [h0, h1886, h1970, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1972 | h1972
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1973 | h1973
                  · linarith only [h0, h1973, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h1967, h1973, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1976 | h1976
                  · linarith only [h0, h1976, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h1967, h1976, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1979 | h1979
            · linarith only [h1, h1967, h1979, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1981 | h1981
              · linarith only [h1, h1886, h1967, h1981, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1983 | h1983
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1984 | h1984
                  · linarith only [h0, h1967, h1984, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1986 | h1986
                    · linarith only [h0, h1886, h1979, h1983, h1986, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1988 | h1988
                      · linarith only [h1, h1886, h1981, h1984, h1988, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1990 | h1990
                        · linarith only [h1, h1886, h1990, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1992 | h1992
                          · linarith only [h1, h1886, h1992, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1994 | h1994
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1995 | h1995
                              · linarith only [h1, h1886, h1984, h1990, h1994, h1995, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1997 | h1997
                                · linarith only [h1, h1886, h1984, h1992, h1995, h1997, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1999 | h1999
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2000 | h2000
                                    · rcases h1bigk with h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1886, h1994, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2001_1, u1elo3]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1886, h1994, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2001_1, u1elo3]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h2, hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1886, hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h0, hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1984, hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1986, hlam, p2001_1]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1988, hlam, p2001_1]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1, hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1, h1886, h1994, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2001_1, u1elo3]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1990, hlam, p2001_1]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1992, hlam, p2001_1]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [hc01, hlam, hphi, p2001_1, u1elo3]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        rcases p2001_3 (m.d 0 1) (by simp) with h2018 | h2018
                                        · linarith only [h2, h2018, hlam]
                                        · linarith only [h0, h2018, hlam]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        rcases p2001_3 (m.d 0 1) (by simp) with h2021 | h2021
                                        · linarith only [h2, h2021, hlam]
                                        · linarith only [h1, h2021, hlam]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1, h1886, h1984, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2001_1, u1elo3]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1, h1984, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2001_1, u1elo4]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        rcases p2001_3 (m.d 0 1) (by simp) with h2027 | h2027
                                        · linarith only [h1886, h2027, hlam]
                                        · linarith only [h0, h2027, hlam]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        rcases p2001_3 (m.d 0 1) (by simp) with h2030 | h2030
                                        · linarith only [h1886, h2030, hlam]
                                        · linarith only [h1, h2030, hlam]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [h1994, hlam, p2001_0]
                                      · obtain ⟨p2001_0, p2001_1, p2001_2, p2001_3⟩ := h2001c
                                        linarith only [hlam, p2001_0]
                                    · linarith only [h0, h1979, h1983, h1995, h2, h2000, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                                  · linarith only [h1, h1983, h1984, h1986, h1999, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                            · linarith only [h1983, h1994, h2, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2038 | h2038
                  · linarith only [h0, h1967, h2038, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2040 | h2040
                    · linarith only [h0, h2, h2040, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2042 | h2042
                      · linarith only [h1, h1981, h2, h2038, h2042, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2044 | h2044
                        · linarith only [h1, h2, h2044, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2046 | h2046
                          · linarith only [h1, h2, h2046, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2048 | h2048
                            · linarith only [h1983, h2, h2048, hc01, hlam, hphi, u1elo3]
                            · linarith only [h1, h2, h2038, h2048, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2051 | h2051
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2052 | h2052
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2053 | h2053
          · linarith only [h0, h1, h2053, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2055 | h2055
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2056 | h2056
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2057 | h2057
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2058 | h2058
                  · linarith only [h2053, h2055, h2058, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2060 | h2060
                    · linarith only [h0, h1, h2060, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h2055, h2060, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2063 | h2063
                  · linarith only [h0, h1, h2053, h2063, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2065 | h2065
                    · linarith only [h0, h1, h2065, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h2055, h2065, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2068 | h2068
                · linarith only [h2055, h2056, h2068, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2070 | h2070
                  · linarith only [h0, h1, h2070, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2072 | h2072
                    · linarith only [h0, h1, h2072, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h1, h2052, h2055, h2056, h2072, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2075 | h2075
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2076 | h2076
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2077 | h2077
                  · linarith only [h0, h1, h2077, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2079 | h2079
                    · linarith only [h0, h1, h2055, h2079, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2081 | h2081
                      · linarith only [h1, h2051, h2079, h2081, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h2055, h2075, h2081, hc12, hc24, hlam, hphi]
                · linarith only [h2055, h2075, h2076, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2085 | h2085
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2086 | h2086
                  · linarith only [h0, h1, h2086, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2088 | h2088
                    · linarith only [h0, h1, h2055, h2088, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2090 | h2090
                      · linarith only [h0, h1, h2075, h2090, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2092 | h2092
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2093 | h2093
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2094 | h2094
                            · linarith only [h1, h2051, h2094, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · linarith only [h1, h2051, h2085, h2088, h2094, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1, h2093, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2051, h2088, h2092, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2099 | h2099
                  · linarith only [h0, h1, h2099, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2101 | h2101
                    · linarith only [h0, h1, h2055, h2101, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2103 | h2103
                      · linarith only [h1, h2051, h2075, h2101, h2103, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2105 | h2105
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2106 | h2106
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2107 | h2107
                            · linarith only [h1, h2051, h2085, h2107, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2109 | h2109
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2110 | h2110
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2111 | h2111
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2112 | h2112
                                    · linarith only [h1, h2052, h2085, h2105, h2107, h2112, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · rcases h1bigk with h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2114_1, u1elo2]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h1, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h1, h2101, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2114_1, u1elo2]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2114_1, u1elo2]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h0, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2099, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2101, hlam, p2114_1]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2103, hlam, p2114_1]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [hc01, hlam, hphi, p2114_1, u1elo2]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        rcases p2114_3 (m.d 0 1) (by simp) with h2126 | h2126
                                        · linarith only [h1, h2126, hlam]
                                        · linarith only [h0, h2126, hlam]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        rcases p2114_3 (m.d 0 1) (by simp) with h2130 | h2130
                                        · linarith only [h1, h2130, hlam]
                                        · linarith only [h2051, h2130, hlam]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        rcases p2114_3 (m.d 0 1) (by simp) with h2133 | h2133
                                        · linarith only [h1, h2133, hlam]
                                        · linarith only [h2052, h2133, hlam]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2051, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2052, h2107, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2114_1, u0elo0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2105, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2107, hlam, p2114_1]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2052, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h1, h2052, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2114_1, u1elo2]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h2106, hlam, p2114_0]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [h1, h2052, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2114_1, u1elo2]
                                      · obtain ⟨p2114_0, p2114_1, p2114_2, p2114_3⟩ := h2114c
                                        linarith only [hlam, p2114_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2146 | h2146
                                    · linarith only [h0, h2055, h2085, h2105, h2146, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                    · rcases h1bigk with h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, h2101, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h0, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2099, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2101, hlam, p2148_1]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2103, hlam, p2148_1]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [hc01, hlam, hphi, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        rcases p2148_3 (m.d 0 1) (by simp) with h2160 | h2160
                                        · linarith only [h1, h2160, hlam]
                                        · linarith only [h0, h2160, hlam]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        rcases p2148_3 (m.d 0 1) (by simp) with h2164 | h2164
                                        · linarith only [h1, h2164, hlam]
                                        · linarith only [h2051, h2164, hlam]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        rcases p2148_3 (m.d 0 1) (by simp) with h2167 | h2167
                                        · linarith only [h1, h2167, hlam]
                                        · linarith only [h2052, h2167, hlam]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2051, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, h2051, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2105, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2107, hlam, p2148_1]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2052, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, h2052, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h2106, hlam, p2148_0]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [h1, h2052, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2148_1, u1elo2]
                                      · obtain ⟨p2148_0, p2148_1, p2148_2, p2148_3⟩ := h2148c
                                        linarith only [hlam, p2148_0]
                                · linarith only [h1, h2052, h2099, h2106, h2110, hlam]
                              · linarith only [h0, h1, h2099, h2109, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h2051, h2101, h2106, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2051, h2101, h2105, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2184 | h2184
          · linarith only [h0, h1, h2184, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2186 | h2186
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2187 | h2187
              · linarith only [h0, h2052, h2187, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2189 | h2189
                · linarith only [h2051, h2052, h2189, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2191 | h2191
                  · linarith only [h2184, h2186, h2191, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2193 | h2193
                    · linarith only [h0, h1, h2193, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h2186, h2187, h2193, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2196 | h2196
              · linarith only [h2051, h2052, h2186, h2196, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2198 | h2198
                · linarith only [h2051, h2052, h2198, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2200 | h2200
                  · linarith only [h0, h1, h2200, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2202 | h2202
                    · linarith only [h0, h1, h2186, h2202, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2204 | h2204
                      · linarith only [h0, h2052, h2196, h2204, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2206 | h2206
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2207 | h2207
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2208 | h2208
                            · linarith only [h2051, h2198, h2208, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2210 | h2210
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2211 | h2211
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2212 | h2212
                                  · linarith only [h2051, h2052, h2202, h2208, h2212, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2214 | h2214
                                    · linarith only [h2051, h2052, h2206, h2207, h2212, h2214, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · rcases h1bigk with h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c | h2216c
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2052, h2207, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2216_1, u1elo2]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h1, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2052, h2207, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2216_1, u1elo2]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2052, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h0, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2200, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2202, hlam, p2216_1]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2204, hlam, p2216_1]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hc01, hlam, hphi, p2216_1, u1elo2]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        rcases p2216_3 (m.d 0 1) (by simp) with h2228 | h2228
                                        · linarith only [h1, h2228, hlam]
                                        · linarith only [h0, h2228, hlam]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        rcases p2216_3 (m.d 0 1) (by simp) with h2232 | h2232
                                        · linarith only [h1, h2232, hlam]
                                        · linarith only [h2051, h2232, hlam]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2051, h2052, h2202, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2216_1, u1elo2]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2051, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2051, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2216_1, u0elo0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2206, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2208, hlam, p2216_1]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hc01, hlam, hphi, p2216_1, u1elo4]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        rcases p2216_3 (m.d 0 1) (by simp) with h2242 | h2242
                                        · linarith only [h2052, h2242, hlam]
                                        · linarith only [h0, h2242, hlam]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [h2207, hlam, p2216_0]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        rcases p2216_3 (m.d 0 1) (by simp) with h2246 | h2246
                                        · linarith only [h2052, h2246, hlam]
                                        · linarith only [h2051, h2246, hlam]
                                      · obtain ⟨p2216_0, p2216_1, p2216_2, p2216_3⟩ := h2216c
                                        linarith only [hlam, p2216_0]
                                · linarith only [h2200, h2207, h2211, hlam]
                              · linarith only [h1, h2051, h2200, h2202, h2210, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h2051, h2202, h2207, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2051, h2202, h2206, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2254 | h2254
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2255 | h2255
          · linarith only [h0, h1, h2255, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2257 | h2257
            · linarith only [h0, h2051, h2257, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2259 | h2259
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2260 | h2260
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2261 | h2261
                  · linarith only [h2255, h2259, h2261, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2263 | h2263
                    · linarith only [h0, h1, h2257, h2259, h2263, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2265 | h2265
                      · linarith only [h0, h1, h2265, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h1, h2259, h2265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h0, h2051, h2259, h2260, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2269 | h2269
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2270 | h2270
                  · linarith only [h0, h1, h2270, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2272 | h2272
                    · linarith only [h0, h1, h2257, h2272, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2274 | h2274
                      · linarith only [h0, h1, h2259, h2274, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2276 | h2276
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2277 | h2277
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2278 | h2278
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2279 | h2279
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2280 | h2280
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2281 | h2281
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2282 | h2282
                                    · rcases h1bigk with h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2051, h2276, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2283_1, u1elo2]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h1, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2051, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2051, h2276, hc15, hlam, hphi, ht01, ht0b, ht5b, p2283_1, u1elo2]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h0, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2270, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2272, hlam, p2283_1]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2274, hlam, p2283_1]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [hc01, hlam, hphi, p2283_1, u1elo2]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        rcases p2283_3 (m.d 0 1) (by simp) with h2295 | h2295
                                        · linarith only [h1, h2295, hlam]
                                        · linarith only [h0, h2295, hlam]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2051, h2254, h2274, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2283_1, u1elo2]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        rcases p2283_3 (m.d 0 1) (by simp) with h2300 | h2300
                                        · linarith only [h1, h2300, hlam]
                                        · linarith only [h2254, h2300, hlam]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2254, h2274, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2283_1, u1elo3]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        rcases p2283_3 (m.d 0 1) (by simp) with h2304 | h2304
                                        · linarith only [h2051, h2304, hlam]
                                        · linarith only [h0, h2304, hlam]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2276, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        rcases p2283_3 (m.d 0 1) (by simp) with h2309 | h2309
                                        · linarith only [h2051, h2309, hlam]
                                        · linarith only [h2254, h2309, hlam]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2254, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2254, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2283_1, u0elo0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2277, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [h2278, hlam, p2283_0]
                                      · obtain ⟨p2283_0, p2283_1, p2283_2, p2283_3⟩ := h2283c
                                        linarith only [hlam, p2283_0]
                                    · linarith only [h2051, h2254, h2276, h2278, h2282, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h2051, h2254, h2272, h2278, h2281, hlam]
                                · linarith only [h0, h2051, h2270, h2276, h2280, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h2051, h2254, h2270, h2274, h2276, h2279, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h2051, h2254, h2274, h2278, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h2051, h2254, h2274, h2276, h2277, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2254, h2274, h2276, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2051, h2254, h2269, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2325 | h2325
          · linarith only [h0, h1, h2325, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2327 | h2327
            · linarith only [h0, h2051, h2327, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2329 | h2329
              · linarith only [h0, h2254, h2329, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2331 | h2331
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2332 | h2332
                  · linarith only [h0, h2325, h2332, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2334 | h2334
                    · linarith only [h0, h1, h2327, h2334, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2336 | h2336
                      · linarith only [h0, h1, h2329, h2336, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2338 | h2338
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2339 | h2339
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2340 | h2340
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2341 | h2341
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2342 | h2342
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2343 | h2343
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2344 | h2344
                                    · rcases h1bigk with h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c | h2345c
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2254, h2338, h2340, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2345_1, u1elo2]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h1, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2051, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2254, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h0, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2332, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2334, hlam, p2345_1]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2336, hlam, p2345_1]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [hc01, hlam, hphi, p2345_1, u1elo2]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        rcases p2345_3 (m.d 0 1) (by simp) with h2357 | h2357
                                        · linarith only [h1, h2357, hlam]
                                        · linarith only [h0, h2357, hlam]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h0, h2051, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2345_1, u1elo2]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h0, h2254, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2345_1, u1elo2]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2345_1, u1elo3]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        rcases p2345_3 (m.d 0 1) (by simp) with h2364 | h2364
                                        · linarith only [h2051, h2364, hlam]
                                        · linarith only [h0, h2364, hlam]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2338, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h0, h2254, h2338, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2345_1, u1elo2]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2345_1, u1elo4]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        rcases p2345_3 (m.d 0 1) (by simp) with h2371 | h2371
                                        · linarith only [h2254, h2371, hlam]
                                        · linarith only [h0, h2371, hlam]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2339, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [h2340, hlam, p2345_0]
                                      · obtain ⟨p2345_0, p2345_1, p2345_2, p2345_3⟩ := h2345c
                                        linarith only [hlam, p2345_0]
                                    · rcases h1bigk with h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2377_1, u1elo2]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h1, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2051, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2254, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h0, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2332, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2334, hlam, p2377_1]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2336, hlam, p2377_1]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [hc01, hlam, hphi, p2377_1, u1elo2]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        rcases p2377_3 (m.d 0 1) (by simp) with h2389 | h2389
                                        · linarith only [h1, h2389, hlam]
                                        · linarith only [h0, h2389, hlam]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h0, h2051, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2377_1, u1elo2]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h0, h2254, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2377_1, u1elo2]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2377_1, u1elo3]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        rcases p2377_3 (m.d 0 1) (by simp) with h2396 | h2396
                                        · linarith only [h2051, h2396, hlam]
                                        · linarith only [h0, h2396, hlam]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2338, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h0, h2254, h2338, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2377_1, u1elo2]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2377_1, u1elo4]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        rcases p2377_3 (m.d 0 1) (by simp) with h2403 | h2403
                                        · linarith only [h2254, h2403, hlam]
                                        · linarith only [h0, h2403, hlam]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2339, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [h2340, hlam, p2377_0]
                                      · obtain ⟨p2377_0, p2377_1, p2377_2, p2377_3⟩ := h2377c
                                        linarith only [hlam, p2377_0]
                                  · linarith only [h0, h2051, h2334, h2343, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h2332, h2342, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h2332, h2341, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h2051, h2331, h2340, hlam]
                          · linarith only [h0, h1, h2339, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h2338, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2415 | h2415
                  · linarith only [h0, h1, h2415, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2417 | h2417
                    · linarith only [h0, h1, h2417, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2419 | h2419
                      · linarith only [h0, h1, h2419, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2421 | h2421
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2422 | h2422
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2423 | h2423
                            · linarith only [h0, h2051, h2331, h2421, h2423, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h0, h2051, h2423, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h2422, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h2421, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2428 | h2428
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2429 | h2429
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2430 | h2430
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2431 | h2431
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2432 | h2432
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2433 | h2433
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2434 | h2434
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2435 | h2435
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2436 | h2436
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2437 | h2437
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2438 | h2438
                        · linarith only [h0, h2428, h2438, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2440 | h2440
                          · linarith only [h0, h2429, h2438, h2440, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2442 | h2442
                            · linarith only [h0, h2429, h2442, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h0, h2429, h2434, h2438, h2442, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h2433, h2437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2432, h2436, hlam]
                  · linarith only [h0, h2431, h2435, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2448 | h2448
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2449 | h2449
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2450 | h2450
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2451 | h2451
                        · linarith only [h0, h2428, h2451, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2453 | h2453
                          · linarith only [h0, h2428, h2453, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2455 | h2455
                            · linarith only [h0, h2429, h2434, h2455, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2457 | h2457
                              · linarith only [h2448, h2451, h2457, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2459 | h2459
                                · linarith only [h2448, h2453, h2459, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2461 | h2461
                                  · linarith only [h2429, h2434, h2449, h2461, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2463 | h2463
                                    · rcases h1bigk with h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c | h2464c
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h0, hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h0, h2448, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2464_1, u1elo1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2464_1, u1elo1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p2464_1, u1elo1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [hc01, hlam, hphi, p2464_1, u1elo1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        rcases p2464_3 (m.d 0 1) (by simp) with h2472 | h2472
                                        · linarith only [h0, h2472, hlam]
                                        · linarith only [h2428, h2472, hlam]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        rcases p2464_3 (m.d 0 1) (by simp) with h2475 | h2475
                                        · linarith only [h0, h2475, hlam]
                                        · linarith only [h2429, h2475, hlam]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        rcases p2464_3 (m.d 0 1) (by simp) with h2478 | h2478
                                        · linarith only [h0, h2478, hlam]
                                        · linarith only [h2430, h2478, hlam]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2428, hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2448, hlam, p2464_1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2451, hlam, p2464_1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2453, hlam, p2464_1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2429, hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2449, hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2430, h2448, h2455, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2464_1, u0elo0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2455, hlam, p2464_1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2430, hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h2450, hlam, p2464_0]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h0, h2430, h2448, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2464_1, u1elo1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [h0, h2430, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2464_1, u1elo1]
                                      · obtain ⟨p2464_0, p2464_1, p2464_2, p2464_3⟩ := h2464c
                                        linarith only [hlam, p2464_0]
                                    · rcases h1bigk with h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h0, hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h0, h2448, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2496_1, u1elo1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h0, h2449, h2457, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2496_1, u1elo1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u1elo1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [hc01, hlam, hphi, p2496_1, u1elo1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        rcases p2496_3 (m.d 0 1) (by simp) with h2504 | h2504
                                        · linarith only [h0, h2504, hlam]
                                        · linarith only [h2428, h2504, hlam]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        rcases p2496_3 (m.d 0 1) (by simp) with h2507 | h2507
                                        · linarith only [h0, h2507, hlam]
                                        · linarith only [h2429, h2507, hlam]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        rcases p2496_3 (m.d 0 1) (by simp) with h2510 | h2510
                                        · linarith only [h0, h2510, hlam]
                                        · linarith only [h2430, h2510, hlam]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2428, hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2448, hlam, p2496_1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2451, hlam, p2496_1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2453, hlam, p2496_1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2429, hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2449, hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2429, h2448, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2496_1, u0elo0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2455, hlam, p2496_1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2430, hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h2450, hlam, p2496_0]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h0, h2430, h2448, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2496_1, u1elo1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [h0, h2430, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2496_1, u1elo1]
                                      · obtain ⟨p2496_0, p2496_1, p2496_2, p2496_3⟩ := h2496c
                                        linarith only [hlam, p2496_0]
                      · linarith only [h0, h2433, h2450, hlam]
                    · linarith only [h0, h2432, h2449, hlam]
                  · linarith only [h0, h2431, h2448, hlam]
              · linarith only [h0, h2430, h2433, hlam]
            · linarith only [h0, h2429, h2432, hlam]
          · linarith only [h0, h2428, h2431, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2534 | h2534
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2535 | h2535
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2536 | h2536
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2537 | h2537
                · linarith only [h2429, h2430, h2537, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2539 | h2539
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2540 | h2540
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2541 | h2541
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2542 | h2542
                        · linarith only [h2428, h2430, h2541, h2542, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2544 | h2544
                          · linarith only [h2429, h2430, h2541, h2542, h2544, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2546 | h2546
                            · linarith only [h2429, h2430, h2537, h2541, h2546, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2548 | h2548
                              · linarith only [h2539, h2542, h2548, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2550 | h2550
                                · linarith only [h2429, h2430, h2539, h2542, h2544, h2550, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2552 | h2552
                                  · linarith only [h2429, h2430, h2540, h2546, h2552, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2554 | h2554
                                    · linarith only [h2429, h2430, h2539, h2542, h2546, h2554, hc23, hc34, hlam, hphi]
                                    · rcases h1bigk with h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h0, hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2430, h2539, h2541, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2556_1, u1elo1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2430, h2541, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2556_1, u1elo1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2430, hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hc01, hlam, hphi, p2556_1, u1elo1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        rcases p2556_3 (m.d 0 1) (by simp) with h2564 | h2564
                                        · linarith only [h0, h2564, hlam]
                                        · linarith only [h2428, h2564, hlam]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        rcases p2556_3 (m.d 0 1) (by simp) with h2567 | h2567
                                        · linarith only [h0, h2567, hlam]
                                        · linarith only [h2429, h2567, hlam]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2429, h2430, h2539, h2542, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2556_1, u1elo1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2428, hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2539, hlam, p2556_1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2542, hlam, p2556_1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2544, hlam, p2556_1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2429, hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2540, hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2429, h2539, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2556_1, u0elo0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2546, hlam, p2556_1]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hc01, hlam, hphi, p2556_1, u1elo4]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [h2541, hlam, p2556_0]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        rcases p2556_3 (m.d 0 1) (by simp) with h2583 | h2583
                                        · linarith only [h2430, h2583, hlam]
                                        · linarith only [h2428, h2583, hlam]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        rcases p2556_3 (m.d 0 1) (by simp) with h2586 | h2586
                                        · linarith only [h2430, h2586, hlam]
                                        · linarith only [h2429, h2586, hlam]
                                      · obtain ⟨p2556_0, p2556_1, p2556_2, p2556_3⟩ := h2556c
                                        linarith only [hlam, p2556_0]
                      · linarith only [h0, h2429, h2536, h2541, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h2535, h2540, hlam]
                  · linarith only [h0, h2534, h2539, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2593 | h2593
                · linarith only [h0, h2429, h2536, h2593, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2595 | h2595
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2596 | h2596
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2597 | h2597
                      · linarith only [h0, h2428, h2536, h2595, h2597, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2599 | h2599
                        · linarith only [h0, h2428, h2597, h2599, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2601 | h2601
                          · linarith only [h0, h2429, h2597, h2599, h2601, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2603 | h2603
                            · linarith only [h0, h2429, h2593, h2597, h2603, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2605 | h2605
                              · linarith only [h2595, h2599, h2605, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2607 | h2607
                                · linarith only [h0, h2429, h2595, h2597, h2599, h2601, h2607, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h2429, h2595, h2597, h2599, h2607, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h2535, h2596, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2430, h2534, h2536, h2595, hc01, hlam, hphi, u1elo4]
            · linarith only [h0, h2429, h2535, hlam]
          · linarith only [h0, h2428, h2534, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2614 | h2614
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2615 | h2615
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2616 | h2616
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2617 | h2617
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2618 | h2618
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2619 | h2619
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2620 | h2620
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2621 | h2621
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2622 | h2622
                        · linarith only [h2428, h2429, h2620, h2622, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2624 | h2624
                          · linarith only [h2428, h2429, h2620, h2624, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2626 | h2626
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2627 | h2627
                              · linarith only [h2429, h2614, h2619, h2622, h2624, h2627, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2629 | h2629
                                · linarith only [h2619, h2624, h2629, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2631 | h2631
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2632 | h2632
                                    · rcases h1bigk with h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h0, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2429, h2619, h2620, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2633_1, u1elo1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2429, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2429, h2620, hc15, hlam, hphi, ht01, ht0b, ht5b, p2633_1, u1elo1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [hc01, hlam, hphi, p2633_1, u1elo1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        rcases p2633_3 (m.d 0 1) (by simp) with h2641 | h2641
                                        · linarith only [h0, h2641, hlam]
                                        · linarith only [h2428, h2641, hlam]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2429, h2614, h2619, h2624, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2633_1, u1elo1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        rcases p2633_3 (m.d 0 1) (by simp) with h2645 | h2645
                                        · linarith only [h0, h2645, hlam]
                                        · linarith only [h2614, h2645, hlam]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2428, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2619, hlam, p2633_1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2622, hlam, p2633_1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2624, hlam, p2633_1]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2614, h2619, h2624, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2633_1, u1elo3]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2620, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        rcases p2633_3 (m.d 0 1) (by simp) with h2655 | h2655
                                        · linarith only [h2429, h2655, hlam]
                                        · linarith only [h2428, h2655, hlam]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        rcases p2633_3 (m.d 0 1) (by simp) with h2659 | h2659
                                        · linarith only [h2429, h2659, hlam]
                                        · linarith only [h2614, h2659, hlam]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2614, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2621, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2614, h2619, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2633_1, u0elo0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [h2626, hlam, p2633_0]
                                      · obtain ⟨p2633_0, p2633_1, p2633_2, p2633_3⟩ := h2633c
                                        linarith only [hlam, p2633_0]
                                    · linarith only [h2429, h2616, h2622, h2631, h2632, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h2429, h2614, h2626, h2631, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                            · linarith only [h2429, h2614, h2619, h2624, h2626, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2617, h2621, hlam]
                    · linarith only [h0, h2616, h2620, hlam]
                  · linarith only [h0, h2615, h2619, hlam]
                · linarith only [h2429, h2614, h2618, hlam]
              · linarith only [h0, h2614, h2617, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2675 | h2675
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2676 | h2676
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2677 | h2677
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2678 | h2678
                    · linarith only [h0, h2616, h2678, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2680 | h2680
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2681 | h2681
                        · linarith only [h0, h2428, h2678, h2681, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2683 | h2683
                          · linarith only [h0, h2428, h2678, h2683, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2685 | h2685
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2686 | h2686
                              · linarith only [h0, h2614, h2677, h2678, h2681, h2683, h2686, hlam]
                              · linarith only [h0, h2614, h2677, h2678, h2683, h2686, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h2614, h2677, h2678, h2683, h2685, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2675, h2680, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2615, h2677, hlam]
                · linarith only [h0, h2614, h2616, h2676, hlam]
              · linarith only [h0, h2614, h2675, hlam]
          · linarith only [h0, h2428, h2615, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2695 | h2695
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2696 | h2696
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2697 | h2697
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2698 | h2698
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2699 | h2699
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2700 | h2700
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2701 | h2701
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2702 | h2702
                        · linarith only [h2428, h2614, h2702, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2704 | h2704
                          · linarith only [h2428, h2429, h2700, h2704, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2706 | h2706
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2707 | h2707
                              · linarith only [h2614, h2695, h2702, h2706, h2707, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2709 | h2709
                                · linarith only [h2428, h2614, h2699, h2704, h2709, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2711 | h2711
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2712 | h2712
                                    · rcases h1bigk with h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h0, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2614, h2699, h2706, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2713_1, u1elo3]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2429, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2614, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [hc01, hlam, hphi, p2713_1, u1elo1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        rcases p2713_3 (m.d 0 1) (by simp) with h2721 | h2721
                                        · linarith only [h0, h2721, hlam]
                                        · linarith only [h2428, h2721, hlam]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2428, h2429, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2713_1, u1elo1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2428, h2614, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2713_1, u1elo1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2428, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2699, hlam, p2713_1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2702, hlam, p2713_1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2704, hlam, p2713_1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2428, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2713_1, u1elo3]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2700, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        rcases p2713_3 (m.d 0 1) (by simp) with h2733 | h2733
                                        · linarith only [h2429, h2733, hlam]
                                        · linarith only [h2428, h2733, hlam]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2428, h2614, h2699, h2700, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2713_1, u1elo1]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2428, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2713_1, u1elo4]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2701, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        rcases p2713_3 (m.d 0 1) (by simp) with h2740 | h2740
                                        · linarith only [h2614, h2740, hlam]
                                        · linarith only [h2428, h2740, hlam]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [h2706, hlam, p2713_0]
                                      · obtain ⟨p2713_0, p2713_1, p2713_2, p2713_3⟩ := h2713c
                                        linarith only [hlam, p2713_0]
                                    · linarith only [h2428, h2429, h2699, h2702, h2711, h2712, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2746 | h2746
                                    · rcases h1bigk with h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h0, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2614, h2699, h2706, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2747_1, u1elo3]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2429, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2614, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [hc01, hlam, hphi, p2747_1, u1elo1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        rcases p2747_3 (m.d 0 1) (by simp) with h2755 | h2755
                                        · linarith only [h0, h2755, hlam]
                                        · linarith only [h2428, h2755, hlam]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2428, h2429, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2747_1, u1elo1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2428, h2614, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2747_1, u1elo1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2428, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2699, hlam, p2747_1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2702, hlam, p2747_1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2704, hlam, p2747_1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2428, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2747_1, u1elo3]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2700, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        rcases p2747_3 (m.d 0 1) (by simp) with h2767 | h2767
                                        · linarith only [h2429, h2767, hlam]
                                        · linarith only [h2428, h2767, hlam]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2428, h2614, h2699, h2700, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2747_1, u1elo1]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2428, h2699, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2747_1, u1elo4]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2701, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        rcases p2747_3 (m.d 0 1) (by simp) with h2774 | h2774
                                        · linarith only [h2614, h2774, hlam]
                                        · linarith only [h2428, h2774, hlam]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [h2706, hlam, p2747_0]
                                      · obtain ⟨p2747_0, p2747_1, p2747_2, p2747_3⟩ := h2747c
                                        linarith only [hlam, p2747_0]
                                    · linarith only [h2428, h2429, h2698, h2699, h2702, h2746, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h2429, h2698, h2706, hlam]
                      · linarith only [h0, h2428, h2697, h2699, h2701, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h2696, h2700, hlam]
                  · linarith only [h0, h2695, h2699, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2784 | h2784
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2785 | h2785
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2786 | h2786
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2787 | h2787
                        · linarith only [h2428, h2429, h2785, h2787, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2789 | h2789
                          · linarith only [h2428, h2429, h2785, h2789, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2791 | h2791
                            · linarith only [h2429, h2698, h2785, h2791, hc01, hlam, hphi, u1elo1]
                            · linarith only [h2428, h2429, h2784, h2791, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2428, h2697, h2784, h2786, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2428, h2696, h2785, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2695, h2784, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2797 | h2797
                · linarith only [h2696, h2697, h2797, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2799 | h2799
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2800 | h2800
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2801 | h2801
                      · linarith only [h2696, h2697, h2801, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2803 | h2803
                        · linarith only [h2428, h2429, h2803, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2805 | h2805
                          · linarith only [h2428, h2429, h2800, h2801, h2805, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2807 | h2807
                            · linarith only [h2428, h2429, h2797, h2799, h2800, h2801, h2807, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h2428, h2429, h2799, h2807, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h2428, h2696, h2799, h2800, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2614, h2695, h2697, h2799, hc01, hlam, hphi, u1elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2812 | h2812
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2813 | h2813
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2814 | h2814
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2815 | h2815
                    · linarith only [h2696, h2812, h2815, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2817 | h2817
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2818 | h2818
                        · linarith only [h0, h2428, h2815, h2818, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2820 | h2820
                          · linarith only [h2428, h2614, h2815, h2817, h2820, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2822 | h2822
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2823 | h2823
                              · linarith only [h2428, h2614, h2814, h2815, h2817, h2818, h2823, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h2428, h2614, h2814, h2815, h2817, h2823, hc23, hc34, hlam, hphi]
                            · linarith only [h2428, h2614, h2813, h2814, h2815, h2817, h2822, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h2428, h2812, h2814, h2817, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2429, h2695, h2696, h2814, hc01, hlam, hphi, u1elo3]
                · linarith only [h2696, h2812, h2813, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2830 | h2830
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2831 | h2831
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2832 | h2832
                    · linarith only [h0, h2428, h2696, h2831, h2832, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2834 | h2834
                      · linarith only [h0, h2428, h2812, h2831, h2832, h2834, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2836 | h2836
                        · linarith only [h0, h2428, h2832, h2836, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2838 | h2838
                          · linarith only [h0, h2428, h2832, h2838, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2840 | h2840
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2841 | h2841
                              · linarith only [h0, h2428, h2831, h2834, h2836, h2840, h2841, hlam]
                              · linarith only [h0, h2428, h2831, h2832, h2841, hc23, hc34, hlam, hphi]
                            · linarith only [h2428, h2429, h2830, h2831, h2840, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2428, h2695, h2831, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2846 | h2846
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2847 | h2847
                    · linarith only [h0, h2428, h2696, h2846, h2847, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2849 | h2849
                      · linarith only [h0, h2428, h2812, h2846, h2847, h2849, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2851 | h2851
                        · linarith only [h0, h2428, h2847, h2851, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2853 | h2853
                          · linarith only [h0, h2428, h2847, h2853, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2855 | h2855
                            · linarith only [h2428, h2429, h2830, h2846, h2855, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · linarith only [h2428, h2429, h2846, h2855, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2695, h2846, hlam]
          · linarith only [h0, h2428, h2695, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2860 | h2860
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2861 | h2861
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2862 | h2862
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2863 | h2863
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2864 | h2864
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2865 | h2865
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2866 | h2866
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2867 | h2867
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2868 | h2868
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2869 | h2869
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2870 | h2870
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2871 | h2871
                            · linarith only [h2428, h2860, h2866, h2871, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h2428, h2860, h2865, h2866, h2871, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h2428, h2861, h2870, hlam]
                        · linarith only [h2428, h2860, h2869, hlam]
                      · linarith only [h2428, h2864, h2866, h2868, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2863, h2867, hlam]
                  · linarith only [h0, h2862, h2866, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2879 | h2879
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2880 | h2880
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2881 | h2881
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2882 | h2882
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2883 | h2883
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2884 | h2884
                            · linarith only [h2860, h2865, h2884, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2886 | h2886
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2887 | h2887
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2888 | h2888
                                  · linarith only [h2863, h2865, h2888, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2890 | h2890
                                    · linarith only [h2860, h2865, h2880, h2886, h2890, hlam]
                                    · rcases h1bigk with h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h0, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2428, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2428, h2880, h2886, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2892_1, u1elo2]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2428, h2880, h2884, h2886, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2892_1, u1elo2]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [hc01, hlam, hphi, p2892_1, u1elo1]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2428, h2861, h2880, h2884, h2886, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2892_1, u1elo1]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        rcases p2892_3 (m.d 0 1) (by simp) with h2901 | h2901
                                        · linarith only [h0, h2901, hlam]
                                        · linarith only [h2860, h2901, hlam]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        rcases p2892_3 (m.d 0 1) (by simp) with h2904 | h2904
                                        · linarith only [h0, h2904, hlam]
                                        · linarith only [h2861, h2904, hlam]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2861, h2880, h2884, h2886, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2892_1, u1elo2]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2879, hlam, p2892_1]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        rcases p2892_3 (m.d 0 1) (by simp) with h2910 | h2910
                                        · linarith only [h2428, h2910, hlam]
                                        · linarith only [h2860, h2910, hlam]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        rcases p2892_3 (m.d 0 1) (by simp) with h2913 | h2913
                                        · linarith only [h2428, h2913, hlam]
                                        · linarith only [h2861, h2913, hlam]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2860, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2880, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2882, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2884, hlam, p2892_1]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2861, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2881, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2883, hlam, p2892_0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [h2861, h2880, h2886, hc34, hlam, hphi, ht0b, ht45, ht5b, p2892_1, u0elo0]
                                      · obtain ⟨p2892_0, p2892_1, p2892_2, p2892_3⟩ := h2892c
                                        linarith only [hlam, p2892_0]
                                · linarith only [h2428, h2861, h2879, h2883, h2887, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · linarith only [h2428, h2860, h2879, h2882, h2886, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h2428, h2861, h2883, hlam]
                        · linarith only [h2428, h2860, h2882, hlam]
                      · linarith only [h0, h2864, h2881, hlam]
                    · linarith only [h0, h2863, h2880, hlam]
                  · linarith only [h0, h2862, h2879, hlam]
              · linarith only [h0, h2861, h2864, hlam]
            · linarith only [h2428, h2860, h2862, h2863, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2935 | h2935
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2936 | h2936
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2937 | h2937
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2938 | h2938
                  · linarith only [h0, h2862, h2938, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2940 | h2940
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2941 | h2941
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2942 | h2942
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2943 | h2943
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2944 | h2944
                            · linarith only [h0, h2860, h2938, h2944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h2860, h2937, h2938, h2944, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h2861, h2938, h2943, hlam]
                        · linarith only [h0, h2860, h2938, h2942, hlam]
                      · linarith only [h0, h2936, h2941, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2935, h2940, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2951 | h2951
                  · linarith only [h0, h2860, h2862, h2951, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2953 | h2953
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2954 | h2954
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2955 | h2955
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2956 | h2956
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2957 | h2957
                            · linarith only [h2860, h2937, h2957, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2959 | h2959
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2960 | h2960
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2961 | h2961
                                  · linarith only [h2860, h2937, h2953, h2961, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2963 | h2963
                                    · linarith only [h2860, h2937, h2953, h2959, h2963, hlam]
                                    · rcases h1bigk with h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h0, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2428, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h0, h2951, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2965_1]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h0, h2951, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2965_1]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2951, hc01, hc23, hlam, hphi, ht12, p2965_1]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2951, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        rcases p2965_3 (m.d 0 1) (by simp) with h2974 | h2974
                                        · linarith only [h0, h2974, hlam]
                                        · linarith only [h2860, h2974, hlam]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        rcases p2965_3 (m.d 0 1) (by simp) with h2977 | h2977
                                        · linarith only [h0, h2977, hlam]
                                        · linarith only [h2861, h2977, hlam]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2861, h2953, h2957, h2959, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2965_1, u1elo2]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h0, h2861, h2953, h2957, h2959, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2965_1, u1elo2]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        rcases p2965_3 (m.d 0 1) (by simp) with h2983 | h2983
                                        · linarith only [h2428, h2983, hlam]
                                        · linarith only [h2860, h2983, hlam]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        rcases p2965_3 (m.d 0 1) (by simp) with h2986 | h2986
                                        · linarith only [h2428, h2986, hlam]
                                        · linarith only [h2861, h2986, hlam]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2860, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2953, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2955, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2957, hlam, p2965_1]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2861, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2954, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2956, hlam, p2965_0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [h2861, h2953, h2959, hc34, hlam, hphi, ht0b, ht45, ht5b, p2965_1, u0elo0]
                                      · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                        linarith only [hlam, p2965_0]
                                · linarith only [h0, h2951, h2960, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h2861, h2951, h2953, h2957, h2959, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h2428, h2861, h2956, hlam]
                        · linarith only [h0, h2428, h2860, h2862, h2951, h2955, hc02, hc23, hlam, hphi]
                      · linarith only [h0, h2936, h2954, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2935, h2953, hlam]
              · linarith only [h0, h2861, h2936, hlam]
            · linarith only [h0, h2860, h2935, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h3007 | h3007
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3008 | h3008
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3009 | h3009
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3010 | h3010
                · linarith only [h2860, h2861, h3010, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3012 | h3012
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3013 | h3013
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3014 | h3014
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3015 | h3015
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3016 | h3016
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3017 | h3017
                            · linarith only [h2860, h3010, h3017, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3019 | h3019
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3020 | h3020
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3021 | h3021
                                  · linarith only [h2860, h2861, h3013, h3017, h3021, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3023 | h3023
                                    · linarith only [h2860, h2861, h3013, h3017, h3019, h3023, hlam]
                                    · rcases h1bigk with h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h0, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2428, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2861, h3012, h3016, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3025_1, u1elo1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2861, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [hc01, hlam, hphi, p3025_1, u1elo1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2428, hc01, hlam, hphi, p3025_1, u1elo1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        rcases p3025_3 (m.d 0 1) (by simp) with h3034 | h3034
                                        · linarith only [h0, h3034, hlam]
                                        · linarith only [h2860, h3034, hlam]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2860, h2861, h3013, h3019, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3025_1, u1elo1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2860, h3013, h3019, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3025_1, u1elo2]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h3012, hlam, p3025_1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        rcases p3025_3 (m.d 0 1) (by simp) with h3041 | h3041
                                        · linarith only [h2428, h3041, hlam]
                                        · linarith only [h2860, h3041, hlam]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2860, h2861, h3012, h3013, h3019, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3025_1, u1elo1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2860, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h3013, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h3015, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h3017, hlam, p3025_1]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h2860, h3013, h3019, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3025_1, u1elo4]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h3014, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [h3016, hlam, p3025_0]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        rcases p3025_3 (m.d 0 1) (by simp) with h3053 | h3053
                                        · linarith only [h2861, h3053, hlam]
                                        · linarith only [h2860, h3053, hlam]
                                      · obtain ⟨p3025_0, p3025_1, p3025_2, p3025_3⟩ := h3025c
                                        linarith only [hlam, p3025_0]
                                · linarith only [h3012, h3016, h3019, h3020, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · linarith only [h2860, h2861, h3012, h3015, h3016, h3019, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3059 | h3059
                            · linarith only [h2428, h2860, h3059, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3061 | h3061
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3062 | h3062
                                · linarith only [h2428, h2860, h3013, h3016, h3061, h3062, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3064 | h3064
                                  · linarith only [h2428, h2860, h3013, h3016, h3059, h3064, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3066 | h3066
                                    · linarith only [h2428, h2860, h3013, h3016, h3059, h3061, h3066, hlam]
                                    · linarith only [h2428, h2860, h3013, h3016, h3061, h3066, hc34, hc45, hlam, hphi]
                              · linarith only [h3015, h3016, h3061, hc23, hc35, hlam, hphi]
                        · linarith only [h2428, h2860, h3015, hlam]
                      · linarith only [h0, h2860, h3009, h3014, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h3008, h3013, hlam]
                  · linarith only [h0, h3007, h3012, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3074 | h3074
                · linarith only [h0, h2860, h3009, h3074, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3076 | h3076
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3077 | h3077
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3078 | h3078
                      · linarith only [h2428, h2860, h3007, h3009, h3077, h3078, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3080 | h3080
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3081 | h3081
                          · linarith only [h3076, h3078, h3081, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3083 | h3083
                            · linarith only [h2428, h2860, h3007, h3009, h3074, h3083, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3085 | h3085
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3086 | h3086
                                · linarith only [h2428, h2860, h3007, h3077, h3081, h3085, h3086, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3088 | h3088
                                  · linarith only [h2428, h2860, h3076, h3077, h3078, h3083, h3088, hlam]
                                  · linarith only [h2428, h2860, h3076, h3077, h3078, h3085, h3088, hc34, hc45, hlam, hphi]
                              · linarith only [h2428, h2860, h3076, h3080, h3085, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h2428, h2860, h3080, hlam]
                    · linarith only [h0, h3008, h3077, hlam]
                  · linarith only [h0, h3007, h3076, hlam]
            · linarith only [h0, h2860, h3008, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3096 | h3096
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3097 | h3097
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3098 | h3098
                · linarith only [h2860, h2861, h3098, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3100 | h3100
                  · linarith only [h2861, h3007, h3097, h3100, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3102 | h3102
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3103 | h3103
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3104 | h3104
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3105 | h3105
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3106 | h3106
                            · linarith only [h2860, h3098, h3106, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3108 | h3108
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3109 | h3109
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3110 | h3110
                                  · linarith only [h2860, h2861, h3102, h3106, h3110, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3112 | h3112
                                    · linarith only [h2860, h2861, h3102, h3106, h3108, h3112, hlam]
                                    · rcases h1bigk with h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h0, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2428, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2861, h3100, h3103, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3114_1, u1elo2]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2861, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3100, hc01, hlam, hphi, p3114_1, u1elo2]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3100, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        rcases p3114_3 (m.d 0 1) (by simp) with h3123 | h3123
                                        · linarith only [h0, h3123, hlam]
                                        · linarith only [h2860, h3123, hlam]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2860, h2861, h3100, h3102, h3108, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3114_1, u1elo2]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2860, h3102, h3108, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3114_1, u1elo2]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h0, h3097, hc25, hlam, hphi, ht01, ht0b, ht5b, p3114_1, u1elo2]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        rcases p3114_3 (m.d 0 1) (by simp) with h3130 | h3130
                                        · linarith only [h2428, h3130, hlam]
                                        · linarith only [h2860, h3130, hlam]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2860, h2861, h3102, h3108, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3114_1, u1elo2]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2860, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3102, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3104, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3106, hlam, p3114_1]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h2860, h3102, h3103, h3108, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3114_1, u1elo1]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3103, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [h3105, hlam, p3114_0]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        rcases p3114_3 (m.d 0 1) (by simp) with h3142 | h3142
                                        · linarith only [h2861, h3142, hlam]
                                        · linarith only [h2860, h3142, hlam]
                                      · obtain ⟨p3114_0, p3114_1, p3114_2, p3114_3⟩ := h3114c
                                        linarith only [hlam, p3114_0]
                                · linarith only [h0, h2860, h3100, h3102, h3108, h3109, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h2860, h2861, h3100, h3102, h3103, h3108, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h3100, h3103, h3105, hlam]
                        · linarith only [h0, h2860, h3100, h3104, hlam]
                      · linarith only [h0, h3097, h3103, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h3096, h3102, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3152 | h3152
                · linarith only [h0, h2860, h3097, h3152, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3154 | h3154
                  · linarith only [h0, h3007, h3154, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3156 | h3156
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3157 | h3157
                      · linarith only [h0, h2860, h3097, h3156, h3157, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3159 | h3159
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3160 | h3160
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3161 | h3161
                            · linarith only [h2860, h3152, h3161, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3163 | h3163
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3164 | h3164
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3165 | h3165
                                  · linarith only [h0, h3096, h3157, h3161, h3165, hlam]
                                  · linarith only [h0, h2860, h3157, h3165, hc14, hc45, hlam, hphi]
                                · linarith only [h0, h2860, h3007, h3156, h3157, h3160, h3163, h3164, hc02, hc25, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · linarith only [h0, h2860, h3154, h3156, h3163, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3170 | h3170
                            · linarith only [h0, h2860, h3170, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3172 | h3172
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3173 | h3173
                                · linarith only [h0, h3154, h3160, h3173, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h2860, h3154, h3156, h3172, h3173, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h2860, h3154, h3156, h3172, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h2860, h3154, h3159, hlam]
                    · linarith only [h0, h2860, h3096, h3156, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h0, h2860, h3096, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3180 | h3180
        · rcases m.htr 0 2 3 (by decide) (by decide) with h3181 | h3181
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3182 | h3182
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3183 | h3183
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3184 | h3184
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3185 | h3185
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3186 | h3186
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3187 | h3187
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3188 | h3188
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3189 | h3189
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3190 | h3190
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3191 | h3191
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3192 | h3192
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3193 | h3193
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3194 | h3194
                                    · linarith only [h3181, h3191, h3194, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h2860, h3180, h3190, h3194, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                                  · linarith only [h2860, h3180, h3185, h3188, h3190, h3193, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                · linarith only [h2860, h3180, h3185, h3188, h3189, h3192, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3199 | h3199
                                · linarith only [h3185, h3188, h3191, h3199, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h2860, h3180, h3185, h3188, h3189, h3199, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h2860, h3184, h3190, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h2860, h3180, h3188, h3189, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3204 | h3204
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3205 | h3205
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3206 | h3206
                              · linarith only [h2428, h3180, h3187, h3188, h3206, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3208 | h3208
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3209 | h3209
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3210 | h3210
                                    · rcases h1bigk with h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h0, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h2428, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h2860, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h2428, h3187, h3208, h3210, hc45, hlam, hphi, ht01, ht0b, ht5b, p3211_1, u1elo2]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [hc01, hlam, hphi, p3211_1, u1elo1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h2428, h3180, h3187, h3208, h3210, hc45, hlam, hphi, ht01, ht0b, ht5b, p3211_1, u1elo1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h2860, h3180, h3187, h3208, h3210, hc45, hlam, hphi, ht01, ht0b, ht5b, p3211_1, u1elo1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        rcases p3211_3 (m.d 0 1) (by simp) with h3221 | h3221
                                        · linarith only [h0, h3221, hlam]
                                        · linarith only [h3180, h3221, hlam]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3180, h3187, h3208, h3210, hc45, hlam, hphi, ht01, ht0b, ht5b, p3211_1, u1elo2]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3185, hlam, p3211_1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3188, hlam, p3211_1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        rcases p3211_3 (m.d 0 1) (by simp) with h3228 | h3228
                                        · linarith only [h2428, h3228, hlam]
                                        · linarith only [h3180, h3228, hlam]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3180, h3186, h3187, h3208, h3210, hc45, hlam, hphi, ht01, ht0b, ht5b, p3211_1, u1elo1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3186, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h2428, h3180, h3186, h3187, h3208, h3210, hc45, hlam, hphi, ht01, ht0b, ht5b, p3211_1, u1elo1]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        rcases p3211_3 (m.d 0 1) (by simp) with h3235 | h3235
                                        · linarith only [h2860, h3235, hlam]
                                        · linarith only [h3180, h3235, hlam]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3180, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3187, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3204, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [h3205, hlam, p3211_0]
                                      · obtain ⟨p3211_0, p3211_1, p3211_2, p3211_3⟩ := h3211c
                                        linarith only [hlam, p3211_0]
                                    · linarith only [h2428, h3184, h3188, h3210, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                                  · linarith only [h2428, h3180, h3186, h3188, h3205, h3206, h3209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · linarith only [h3188, h3204, h3208, hc23, hc34, hlam, hphi]
                            · linarith only [h2428, h3182, h3184, h3188, h3205, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h2428, h3180, h3204, hlam]
                      · linarith only [h0, h3183, h3187, hlam]
                    · linarith only [h0, h3182, h3186, hlam]
                  · linarith only [h0, h3181, h3185, hlam]
                · linarith only [h2860, h3180, h3184, hlam]
              · linarith only [h0, h3180, h3183, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3253 | h3253
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3254 | h3254
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3255 | h3255
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3256 | h3256
                    · linarith only [h3181, h3182, h3256, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3258 | h3258
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3259 | h3259
                        · linarith only [h3255, h3256, h3259, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3261 | h3261
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3262 | h3262
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3263 | h3263
                              · linarith only [h2428, h3180, h3258, h3259, h3263, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3265 | h3265
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3266 | h3266
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3267 | h3267
                                    · rcases h1bigk with h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h0, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h2428, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h2860, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h2428, h3255, h3256, h3258, h3263, h3265, h3267, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3268_1]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3256, h3263, hc01, hc34, hlam, hphi, ht12, ht23, p3268_1]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3256, h3263, hc13, hc34, hlam, hphi, p3268_1]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3256, hlam, p3268_1]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        rcases p3268_3 (m.d 0 1) (by simp) with h3278 | h3278
                                        · linarith only [h0, h3278, hlam]
                                        · linarith only [h3180, h3278, hlam]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3180, h3258, h3265, h3267, hc45, hlam, hphi, ht01, ht0b, ht5b, p3268_1, u1elo2]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3255, hlam, p3268_1]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3259, hlam, p3268_1]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        rcases p3268_3 (m.d 0 1) (by simp) with h3285 | h3285
                                        · linarith only [h2428, h3285, hlam]
                                        · linarith only [h3180, h3285, hlam]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3180, h3258, h3265, h3267, hc45, hlam, hphi, ht01, ht0b, ht5b, p3268_1, u1elo3]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h0, h3180, h3258, h3265, h3267, hc45, hlam, hphi, ht01, ht0b, ht5b, p3268_1, u1elo3]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h2428, h3180, h3258, h3265, h3267, hc45, hlam, hphi, ht01, ht0b, ht5b, p3268_1, u1elo3]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        rcases p3268_3 (m.d 0 1) (by simp) with h3292 | h3292
                                        · linarith only [h2860, h3292, hlam]
                                        · linarith only [h3180, h3292, hlam]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3180, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3258, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3261, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [h3262, hlam, p3268_0]
                                      · obtain ⟨p3268_0, p3268_1, p3268_2, p3268_3⟩ := h3268c
                                        linarith only [hlam, p3268_0]
                                    · linarith only [h3181, h3182, h3263, h3267, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h2428, h3180, h3255, h3256, h3262, h3266, hlam]
                                · linarith only [h3255, h3256, h3261, h3263, h3265, hc23, hc34, hlam, hphi]
                            · linarith only [h2860, h3254, h3262, hlam]
                          · linarith only [h2428, h3180, h3261, hlam]
                      · linarith only [h2428, h3253, h3255, h3258, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h3181, h3182, h3255, hc12, hc24, hlam, hphi]
                · linarith only [h0, h3180, h3182, h3254, hlam]
              · linarith only [h2428, h3180, h3181, h3253, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3309 | h3309
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3310 | h3310
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3311 | h3311
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3312 | h3312
                  · linarith only [h3181, h3309, h3312, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3314 | h3314
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3315 | h3315
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3316 | h3316
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3317 | h3317
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3318 | h3318
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3319 | h3319
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3320 | h3320
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3321 | h3321
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3322 | h3322
                                    · rcases h1bigk with h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c | h3323c
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h0, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h2428, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h2860, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h0, h3312, h3315, h3320, h3322, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3323_1]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3312, hc01, hc23, hlam, hphi, ht12, p3323_1]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3312, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h2860, h3312, hc01, hc23, hlam, hphi, ht12, p3323_1]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        rcases p3323_3 (m.d 0 1) (by simp) with h3333 | h3333
                                        · linarith only [h0, h3333, hlam]
                                        · linarith only [h3180, h3333, hlam]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3180, h3315, h3320, h3322, hc45, hlam, hphi, ht01, ht0b, ht5b, p3323_1, u1elo2]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h0, h3180, h3315, h3320, h3322, hc45, hlam, hphi, ht01, ht0b, ht5b, p3323_1, u1elo2]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h2860, h3180, h3315, h3320, h3322, hc45, hlam, hphi, ht01, ht0b, ht5b, p3323_1, u1elo2]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        rcases p3323_3 (m.d 0 1) (by simp) with h3340 | h3340
                                        · linarith only [h2428, h3340, hlam]
                                        · linarith only [h3180, h3340, hlam]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3180, h3314, h3315, h3320, h3322, hc45, hlam, hphi, ht01, ht0b, ht5b, p3323_1, u1elo1]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3314, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3316, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        rcases p3323_3 (m.d 0 1) (by simp) with h3347 | h3347
                                        · linarith only [h2860, h3347, hlam]
                                        · linarith only [h3180, h3347, hlam]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3180, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3315, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3317, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [h3318, hlam, p3323_0]
                                      · obtain ⟨p3323_0, p3323_1, p3323_2, p3323_3⟩ := h3323c
                                        linarith only [hlam, p3323_0]
                                    · linarith only [h2860, h3180, h3312, h3314, h3318, h3322, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h2860, h3180, h3312, h3314, h3318, h3319, h3321, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h2860, h3312, h3314, h3320, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h2860, h3180, h3312, h3314, h3318, h3319, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h2860, h3311, h3318, hlam]
                          · linarith only [h2860, h3180, h3314, h3316, h3317, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h3312, h3314, h3316, hlam]
                      · linarith only [h2860, h3310, h3314, h3315, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h3180, h3309, h3314, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h2860, h3180, h3311, hlam]
              · linarith only [h0, h3180, h3310, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3366 | h3366
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3367 | h3367
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3368 | h3368
                  · linarith only [h0, h3180, h3181, h3368, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3370 | h3370
                    · linarith only [h0, h3180, h3309, h3370, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3372 | h3372
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3373 | h3373
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3374 | h3374
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3375 | h3375
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3376 | h3376
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3377 | h3377
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3378 | h3378
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3379 | h3379
                                    · rcases h1bigk with h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h0, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h2428, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h2860, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h0, h3370, h3372, h3373, h3377, h3379, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo2]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3370, h3373, hc01, hlam, hphi, p3380_1, u1elo2]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3368, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3370, hlam, p3380_1]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        rcases p3380_3 (m.d 0 1) (by simp) with h3390 | h3390
                                        · linarith only [h0, h3390, hlam]
                                        · linarith only [h3180, h3390, hlam]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3180, h3372, h3377, h3379, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo2]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h0, h3180, h3372, h3377, h3379, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo2]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h2860, h3180, h3372, h3377, h3379, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo2]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        rcases p3380_3 (m.d 0 1) (by simp) with h3397 | h3397
                                        · linarith only [h2428, h3397, hlam]
                                        · linarith only [h3180, h3397, hlam]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3180, h3372, h3377, h3379, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo3]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h0, h3180, h3372, h3377, h3379, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo3]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3373, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        rcases p3380_3 (m.d 0 1) (by simp) with h3404 | h3404
                                        · linarith only [h2860, h3404, hlam]
                                        · linarith only [h3180, h3404, hlam]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3180, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3372, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3374, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [h3375, hlam, p3380_0]
                                      · obtain ⟨p3380_0, p3380_1, p3380_2, p3380_3⟩ := h3380c
                                        linarith only [hlam, p3380_0]
                                    · linarith only [h0, h3180, h3370, h3373, h3375, h3379, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h0, h3180, h3370, h3375, h3378, hlam]
                                · linarith only [h0, h3370, h3376, h3377, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h3368, h3376, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2860, h3180, h3367, h3372, h3375, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h0, h3180, h3373, h3374, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3418 | h3418
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3419 | h3419
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3420 | h3420
                              · linarith only [h0, h3368, h3373, h3420, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h3180, h3368, h3372, h3420, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h2860, h3367, h3419, hlam]
                          · linarith only [h0, h3180, h3368, h3418, hlam]
                      · linarith only [h0, h3366, h3372, hlam]
                · linarith only [h2860, h3180, h3367, hlam]
              · linarith only [h0, h3180, h3366, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h3428 | h3428
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3429 | h3429
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3430 | h3430
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3431 | h3431
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3432 | h3432
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3433 | h3433
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3434 | h3434
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3435 | h3435
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3436 | h3436
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3437 | h3437
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3438 | h3438
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3439 | h3439
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3440 | h3440
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3441 | h3441
                                    · linarith only [h3428, h3438, h3441, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h0, h3428, h3438, h3440, h3441, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3444 | h3444
                                    · linarith only [h3438, h3440, h3444, hlam]
                                    · rcases h1bigk with h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h0, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h2428, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h2860, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3180, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hc01, hlam, hphi, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h2860, h3431, h3435, h3438, h3440, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h2860, h3431, h3438, h3440, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3180, hc01, hlam, hphi, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hc01, hlam, hphi, p3446_1, u1elo2]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3432, hlam, p3446_1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h2860, h3431, h3432, h3438, h3440, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3180, h3432, hc01, hlam, hphi, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hc01, hlam, hphi, p3446_1, u1elo3]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3433, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3435, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3180, h3432, h3435, hc01, hlam, hphi, p3446_1, u1elo1]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hc01, hlam, hphi, p3446_1, u1elo4]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3434, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3436, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [h3437, hlam, p3446_0]
                                      · obtain ⟨p3446_0, p3446_1, p3446_2, p3446_3⟩ := h3446c
                                        linarith only [hlam, p3446_0]
                                · linarith only [h3432, h3436, h3438, h3439, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3473 | h3473
                                · linarith only [h3432, h3435, h3438, h3473, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3475 | h3475
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3476 | h3476
                                    · rcases h1bigk with h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h0, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h2428, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h2860, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3180, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hc01, hlam, hphi, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3435, h3473, h3476, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h2860, hc01, hlam, hphi, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3180, hc01, hlam, hphi, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hc01, hlam, hphi, p3477_1, u1elo2]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3432, hlam, p3477_1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3180, h3432, h3437, hc01, hlam, hphi, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3180, h3432, hc01, hlam, hphi, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hc01, hlam, hphi, p3477_1, u1elo3]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3433, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3435, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3180, h3432, h3435, hc01, hlam, hphi, p3477_1, u1elo1]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hc01, hlam, hphi, p3477_1, u1elo4]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3434, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3436, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [h3437, hlam, p3477_0]
                                      · obtain ⟨p3477_0, p3477_1, p3477_2, p3477_3⟩ := h3477c
                                        linarith only [hlam, p3477_0]
                                    · linarith only [h2860, h3431, h3432, h3435, h3438, h3476, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3504 | h3504
                                    · linarith only [h3432, h3435, h3475, h3504, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                    · linarith only [h2860, h3431, h3432, h3435, h3438, h3504, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h2860, h3180, h3431, h3437, hc01, hlam, hphi, u1elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3508 | h3508
                            · linarith only [h3435, h3436, h3508, hlam]
                            · linarith only [h2860, h3431, h3508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3511 | h3511
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3512 | h3512
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3513 | h3513
                              · linarith only [h2428, h3435, h3513, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3515 | h3515
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3516 | h3516
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3517 | h3517
                                    · rcases h1bigk with h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h0, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h2428, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h2860, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3180, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hc01, hlam, hphi, p3518_1, u1elo1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h2428, hc01, hlam, hphi, p3518_1, u1elo1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h2860, hc01, hlam, hphi, p3518_1, u1elo1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3180, hc01, hlam, hphi, p3518_1, u1elo1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hc01, hlam, hphi, p3518_1, u1elo2]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3432, hlam, p3518_1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3435, hlam, p3518_1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3180, hc01, hlam, hphi, p3518_1, u1elo2]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hc01, hlam, hphi, p3518_1, u1elo3]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3433, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h2428, hc01, hlam, hphi, p3518_1, u1elo3]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3180, h3433, hc01, hlam, hphi, p3518_1, u1elo1]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3511, hc01, hlam, hphi, p3518_1, u1elo2]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3434, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3511, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [h3512, hlam, p3518_0]
                                      · obtain ⟨p3518_0, p3518_1, p3518_2, p3518_3⟩ := h3518c
                                        linarith only [hlam, p3518_0]
                                    · linarith only [h2428, h3435, h3517, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h0, h3429, h3431, h3513, h3515, h3516, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h3435, h3511, h3515, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h2860, h3429, h3431, h3512, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3548 | h3548
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3549 | h3549
                              · linarith only [h2428, h3435, h3549, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3551 | h3551
                                · linarith only [h0, h2428, h3429, h3511, h3549, h3551, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3553 | h3553
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3554 | h3554
                                    · rcases h1bigk with h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h0, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2428, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2860, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3180, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2428, hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2860, hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2428, h3511, hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hc01, hlam, hphi, p3555_1, u1elo2]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3432, hlam, p3555_1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3435, hlam, p3555_1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3511, hlam, p3555_1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hc01, hlam, hphi, p3555_1, u1elo3]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3433, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2428, h3433, hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3180, h3433, hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hc01, hlam, hphi, p3555_1, u1elo4]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3434, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h2428, h3434, hc01, hlam, hphi, p3555_1, u1elo1]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [h3548, hlam, p3555_0]
                                      · obtain ⟨p3555_0, p3555_1, p3555_2, p3555_3⟩ := h3555c
                                        linarith only [hlam, p3555_0]
                                    · linarith only [h0, h3429, h3553, h3554, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3582 | h3582
                                    · rcases h1bigk with h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h0, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2428, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2860, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3180, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2428, hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2860, hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3180, hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hc01, hlam, hphi, p3583_1, u1elo2]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3432, hlam, p3583_1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3435, hlam, p3583_1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3511, hlam, p3583_1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hc01, hlam, hphi, p3583_1, u1elo3]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3433, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2428, h3433, hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2428, h3433, h3511, hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hc01, hlam, hphi, p3583_1, u1elo4]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3434, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h2428, h3434, hc01, hlam, hphi, p3583_1, u1elo1]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [h3548, hlam, p3583_0]
                                      · obtain ⟨p3583_0, p3583_1, p3583_2, p3583_3⟩ := h3583c
                                        linarith only [hlam, p3583_0]
                                    · linarith only [h0, h2428, h3429, h3431, h3435, h3582, hc01, hlam, hphi, u1elo1]
                            · linarith only [h0, h2860, h3429, h3431, h3548, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h3430, h3434, hlam]
                    · linarith only [h0, h3429, h3433, hlam]
                  · linarith only [h0, h3428, h3432, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3614 | h3614
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3615 | h3615
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3616 | h3616
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3617 | h3617
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3618 | h3618
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3619 | h3619
                            · linarith only [h2860, h3431, h3617, h3619, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3621 | h3621
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3622 | h3622
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3623 | h3623
                                  · linarith only [h2860, h3429, h3619, h3623, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3625 | h3625
                                    · linarith only [h0, h2860, h3428, h3619, h3621, h3625, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                    · rcases h1bigk with h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c | h3627c
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h0, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h2428, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h2860, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3180, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h2428, hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h2860, hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3180, hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hc01, hlam, hphi, p3627_1, u1elo2]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3614, hlam, p3627_1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h2860, h3614, hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3180, h3614, hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hc01, hlam, hphi, p3627_1, u1elo3]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3615, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3617, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3619, hlam, p3627_1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hc01, hlam, hphi, p3627_1, u1elo4]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3616, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h3618, hlam, p3627_0]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [h2860, h3614, h3618, hc01, hlam, hphi, p3627_1, u1elo1]
                                      · obtain ⟨p3627_0, p3627_1, p3627_2, p3627_3⟩ := h3627c
                                        linarith only [hlam, p3627_0]
                                · linarith only [h3614, h3618, h3621, h3622, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3654 | h3654
                                · linarith only [h3614, h3617, h3621, h3654, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3656 | h3656
                                  · linarith only [h0, h3429, h3431, h3656, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3658 | h3658
                                    · linarith only [h3614, h3617, h3619, h3658, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                    · rcases h1bigk with h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h0, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h2428, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h2860, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3180, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hc01, hlam, hphi, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3618, h3621, h3658, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h2860, hc01, hlam, hphi, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3180, hc01, hlam, hphi, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hc01, hlam, hphi, p3660_1, u1elo2]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3614, hlam, p3660_1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h2860, h3614, hc01, hlam, hphi, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3180, h3614, hc01, hlam, hphi, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hc01, hlam, hphi, p3660_1, u1elo3]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3615, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3617, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3619, hlam, p3660_1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hc01, hlam, hphi, p3660_1, u1elo4]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3616, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h3618, hlam, p3660_0]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [h2860, h3614, h3618, hc01, hlam, hphi, p3660_1, u1elo1]
                                      · obtain ⟨p3660_0, p3660_1, p3660_2, p3660_3⟩ := h3660c
                                        linarith only [hlam, p3660_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3686 | h3686
                            · linarith only [h2860, h3431, h3686, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3688 | h3688
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3689 | h3689
                                · linarith only [h2428, h3618, h3689, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3691 | h3691
                                  · linarith only [h2860, h3429, h3686, h3691, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3693 | h3693
                                    · linarith only [h2860, h3686, h3693, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · rcases h1bigk with h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c | h3695c
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h0, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2428, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2860, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3180, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2860, h3617, hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2860, hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2860, h3617, h3618, hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hc01, hlam, hphi, p3695_1, u1elo2]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3614, hlam, p3695_1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2860, h3618, h3693, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3695_1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3618, hlam, p3695_1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hc01, hlam, hphi, p3695_1, u1elo3]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3615, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3617, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3686, hlam, p3695_1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3616, hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h3616, hlam, p3695_0]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2428, h3616, hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [h2860, h3616, hc01, hlam, hphi, p3695_1, u1elo1]
                                      · obtain ⟨p3695_0, p3695_1, p3695_2, p3695_3⟩ := h3695c
                                        linarith only [hlam, p3695_0]
                              · linarith only [h3617, h3618, h3688, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3722 | h3722
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3723 | h3723
                            · linarith only [h2860, h3431, h3723, hc01, hlam, hphi, u1elo3]
                            · linarith only [h3617, h3722, h3723, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3726 | h3726
                            · linarith only [h2860, h3431, h3726, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3728 | h3728
                              · linarith only [h2428, h3617, h3728, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3730 | h3730
                                · linarith only [h0, h2428, h3429, h3722, h3728, h3730, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3732 | h3732
                                  · linarith only [h3429, h3431, h3732, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3734 | h3734
                                    · linarith only [h2428, h3617, h3726, h3734, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h2428, h3617, h3734, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h3430, h3616, hlam]
                    · linarith only [h0, h2860, h3429, h3615, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h3428, h3614, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3740 | h3740
                · linarith only [h3429, h3430, h3740, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3742 | h3742
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3743 | h3743
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3744 | h3744
                      · linarith only [h3428, h3430, h3744, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3746 | h3746
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3747 | h3747
                          · linarith only [h3742, h3744, h3747, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3749 | h3749
                            · linarith only [h2860, h3740, h3749, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3751 | h3751
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3752 | h3752
                                · linarith only [h3428, h3747, h3752, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3754 | h3754
                                  · linarith only [h2860, h3749, h3754, hc01, hc24, hlam, hphi, ht12]
                                  · linarith only [h0, h3428, h3744, h3751, h3754, hc34, hc45, hlam, hphi]
                              · linarith only [h3746, h3747, h3751, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3758 | h3758
                          · linarith only [h3743, h3744, h3746, h3758, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3760 | h3760
                            · linarith only [h2860, h3740, h3743, h3744, h3760, hc01, hc25, hlam, hphi, ht12]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3762 | h3762
                              · linarith only [h2428, h3746, h3762, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3764 | h3764
                                · linarith only [h2428, h3429, h3758, h3762, h3764, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3766 | h3766
                                  · linarith only [h3429, h3740, h3766, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3768 | h3768
                                    · linarith only [h0, h3429, h3744, h3762, h3766, h3768, hc23, hc34, hlam, hphi]
                                    · linarith only [h2428, h3746, h3768, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h3429, h3743, hlam]
                  · linarith only [h0, h3428, h3742, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3773 | h3773
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3774 | h3774
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3775 | h3775
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3776 | h3776
                    · linarith only [h3428, h3429, h3776, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3778 | h3778
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3779 | h3779
                        · linarith only [h3775, h3776, h3779, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3781 | h3781
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3782 | h3782
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3783 | h3783
                              · linarith only [h3428, h3779, h3783, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3785 | h3785
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3786 | h3786
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3787 | h3787
                                    · rcases h1bigk with h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h0, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h2428, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h2860, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3180, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3776, h3783, hc01, hc34, hlam, hphi, ht12, ht23, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3180, h3776, h3781, h3783, hc01, hc34, hlam, hphi, ht12, ht23, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3776, hlam, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3180, h3776, h3783, hc01, hc34, hlam, hphi, ht12, ht23, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hc01, hlam, hphi, p3788_1, u1elo2]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3775, hlam, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3779, hlam, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3180, h3775, h3776, h3783, hc01, hc34, hlam, hphi, ht12, ht23, p3788_1]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hc01, hlam, hphi, p3788_1, u1elo3]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h0, h3428, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3788_1, u1elo3]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h2428, hc01, hlam, hphi, p3788_1, u1elo3]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3180, hc01, hlam, hphi, p3788_1, u1elo3]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3781, hc01, hlam, hphi, p3788_1, u1elo2]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3778, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3781, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [h3782, hlam, p3788_0]
                                      · obtain ⟨p3788_0, p3788_1, p3788_2, p3788_3⟩ := h3788c
                                        linarith only [hlam, p3788_0]
                                    · linarith only [h0, h3428, h3776, h3783, h3785, h3787, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h0, h2860, h3428, h3774, h3776, h3785, h3786, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                                · linarith only [h3775, h3776, h3781, h3783, h3785, hc23, hc34, hlam, hphi]
                            · linarith only [h2860, h3774, h3782, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3818 | h3818
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3819 | h3819
                              · linarith only [h2428, h3428, h3779, h3819, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3821 | h3821
                                · linarith only [h0, h2428, h3428, h3776, h3781, h3819, h3821, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3823 | h3823
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3824 | h3824
                                    · rcases h1bigk with h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c | h3825c
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h0, hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2428, hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2860, hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3180, hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3776, h3819, hc01, hc34, hlam, hphi, ht12, ht23, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2428, h3776, h3819, hc01, hc34, hlam, hphi, ht12, ht23, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3776, hlam, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2428, h3776, h3781, h3819, hc01, hc34, hlam, hphi, ht12, ht23, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hc01, hlam, hphi, p3825_1, u1elo2]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3775, hlam, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3779, hlam, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3781, hlam, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hc01, hlam, hphi, p3825_1, u1elo3]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h0, h3773, h3821, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3825_1, u1elo3]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2428, hc01, hlam, hphi, p3825_1, u1elo3]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2428, h3781, hc01, hlam, hphi, p3825_1, u1elo3]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3778, hc01, hlam, hphi, p3825_1, u1elo1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3778, hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h2428, h3776, h3778, h3819, hc01, hc34, hlam, hphi, ht12, ht23, p3825_1]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [h3818, hlam, p3825_0]
                                      · obtain ⟨p3825_0, p3825_1, p3825_2, p3825_3⟩ := h3825c
                                        linarith only [hlam, p3825_0]
                                    · linarith only [h0, h3773, h3776, h3819, h3823, h3824, hlam]
                                  · linarith only [h0, h3773, h3776, h3821, h3823, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h2860, h3773, h3774, h3818, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h3773, h3778, hlam]
                  · linarith only [h0, h3428, h3775, hlam]
                · linarith only [h3429, h3773, h3774, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3857 | h3857
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3858 | h3858
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3859 | h3859
                    · linarith only [h3428, h3429, h3859, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3861 | h3861
                      · linarith only [h3428, h3773, h3859, h3861, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3863 | h3863
                        · linarith only [h3858, h3859, h3863, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3865 | h3865
                          · linarith only [h3858, h3861, h3865, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3867 | h3867
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3868 | h3868
                              · linarith only [h3428, h3863, h3868, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3870 | h3870
                                · linarith only [h0, h2428, h3428, h3859, h3865, h3868, h3870, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3872 | h3872
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3873 | h3873
                                    · rcases h1bigk with h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h0, hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h2428, hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h2860, hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3180, hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3861, h3868, h3872, hc01, hc34, hlam, hphi, ht12, ht23, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h2428, h3861, h3868, h3872, hc01, hc34, hlam, hphi, ht12, ht23, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3859, hlam, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3861, hlam, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hc01, hlam, hphi, p3874_1, u1elo2]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3858, hlam, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3863, hlam, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3865, hlam, p3874_1]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hc01, hlam, hphi, p3874_1, u1elo3]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h0, h3428, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3874_1, u1elo3]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h2428, hc01, hlam, hphi, p3874_1, u1elo3]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3180, hc01, hlam, hphi, p3874_1, u1elo3]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hc01, hlam, hphi, p3874_1, u1elo4]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h2428, h3858, hc01, hlam, hphi, p3874_1, u1elo4]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h2428, hc01, hlam, hphi, p3874_1, u1elo4]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [h3867, hlam, p3874_0]
                                      · obtain ⟨p3874_0, p3874_1, p3874_2, p3874_3⟩ := h3874c
                                        linarith only [hlam, p3874_0]
                                    · linarith only [h2860, h3428, h3429, h3857, h3868, h3873, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                                  · linarith only [h2428, h2860, h3857, h3858, h3859, h3872, hc01, hlam, hphi, u1elo3]
                            · linarith only [h2860, h3857, h3867, hlam]
                  · linarith only [h0, h3428, h3858, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3904 | h3904
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3905 | h3905
                    · linarith only [h3428, h3429, h3905, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3907 | h3907
                      · linarith only [h3428, h3773, h3905, h3907, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3909 | h3909
                        · linarith only [h3904, h3905, h3909, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3911 | h3911
                          · linarith only [h3904, h3907, h3911, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3913 | h3913
                            · linarith only [h3428, h3429, h3857, h3913, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3915 | h3915
                              · linarith only [h0, h3428, h3905, h3913, h3915, hc34, hc45, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3917 | h3917
                                · linarith only [h0, h3428, h3905, h3911, h3913, h3917, hc13, hc45, hlam, hphi, ht34]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3919 | h3919
                                  · linarith only [h2428, h3904, h3905, h3913, h3915, h3919, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h3428, h3429, h3919, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h3428, h3429, h3904, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3923 | h3923
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3924 | h3924
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3925 | h3925
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3926 | h3926
                  · linarith only [h3428, h3923, h3926, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3928 | h3928
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3929 | h3929
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3930 | h3930
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3931 | h3931
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3932 | h3932
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3933 | h3933
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3934 | h3934
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3935 | h3935
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3936 | h3936
                                    · rcases h1bigk with h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h0, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h2428, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h2860, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3180, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3926, hc01, hc23, hlam, hphi, ht12, p3937_1]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3926, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h2860, h3926, hc01, hc23, hlam, hphi, ht12, p3937_1]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3180, h3926, hc01, hc23, hlam, hphi, ht12, p3937_1]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hc01, hlam, hphi, p3937_1, u1elo2]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h0, hc01, hlam, hphi, p3937_1, u1elo2]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h2860, hc01, hlam, hphi, p3937_1, u1elo2]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3180, hc01, hlam, hphi, p3937_1, u1elo2]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hc01, hlam, hphi, p3937_1, u1elo3]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3928, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3930, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3180, h3928, hc01, hlam, hphi, p3937_1, u1elo1]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hc01, hlam, hphi, p3937_1, u1elo4]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3929, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3931, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [h3932, hlam, p3937_0]
                                      · obtain ⟨p3937_0, p3937_1, p3937_2, p3937_3⟩ := h3937c
                                        linarith only [hlam, p3937_0]
                                    · linarith only [h0, h3923, h3926, h3935, h3936, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3964 | h3964
                                    · linarith only [h3930, h3935, h3964, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · rcases h1bigk with h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c | h3966c
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h0, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h2428, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h2860, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3180, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3926, hc01, hc23, hlam, hphi, ht12, p3966_1]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3926, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h2860, h3926, hc01, hc23, hlam, hphi, ht12, p3966_1]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3180, h3926, hc01, hc23, hlam, hphi, ht12, p3966_1]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hc01, hlam, hphi, p3966_1, u1elo2]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h0, h3923, h3925, h3935, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3966_1, u1elo2]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h2860, h3925, h3933, h3935, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3966_1, u1elo2]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3180, hc01, hlam, hphi, p3966_1, u1elo2]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hc01, hlam, hphi, p3966_1, u1elo3]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3928, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3930, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3180, h3926, h3928, hc01, hc23, hlam, hphi, ht12, p3966_1]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hc01, hlam, hphi, p3966_1, u1elo4]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3929, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3931, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [h3932, hlam, p3966_0]
                                      · obtain ⟨p3966_0, p3966_1, p3966_2, p3966_3⟩ := h3966c
                                        linarith only [hlam, p3966_0]
                                · linarith only [h0, h3926, h3934, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h3926, h3933, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2860, h3923, h3925, h3926, h3932, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h3926, h3929, h3931, hlam]
                        · linarith only [h3926, h3928, h3930, hlam]
                      · linarith only [h0, h2428, h3428, h3924, h3929, hc01, hlam, hphi, u1elo2]
                    · linarith only [h0, h3923, h3928, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3999 | h3999
                  · linarith only [h3428, h3923, h3999, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4001 | h4001
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4002 | h4002
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4003 | h4003
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4004 | h4004
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4005 | h4005
                            · linarith only [h2860, h3925, h4001, h4005, hc01, hlam, hphi, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4007 | h4007
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4008 | h4008
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4009 | h4009
                                  · linarith only [h3923, h3925, h4009, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4011 | h4011
                                    · linarith only [h2860, h4005, h4011, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · rcases h1bigk with h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h0, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2428, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2860, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h3180, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h3999, hc01, hc23, hlam, hphi, ht12, p4013_1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h3999, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2860, h3999, hc01, hc23, hlam, hphi, ht12, p4013_1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2860, h3999, h4005, hc01, hc23, hlam, hphi, ht12, p4013_1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [hc01, hlam, hphi, p4013_1, u1elo2]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h0, h3924, h4009, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4013_1, u1elo2]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2860, hc01, hlam, hphi, p4013_1, u1elo2]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2860, h4005, hc01, hlam, hphi, p4013_1, u1elo2]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h4002, h4005, hc01, hlam, hphi, p4013_1, u1elo1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h4001, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h4003, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h4005, hlam, p4013_1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h3999, h4002, hc01, hc23, hlam, hphi, ht12, p4013_1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h4002, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h4004, hlam, p4013_0]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [h2860, h3999, h4002, hc01, hc23, hlam, hphi, ht12, p4013_1]
                                      · obtain ⟨p4013_0, p4013_1, p4013_2, p4013_3⟩ := h4013c
                                        linarith only [hlam, p4013_0]
                                · linarith only [h0, h3999, h4008, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h2860, h3999, h4002, h4005, h4007, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h3999, h4002, h4004, hlam]
                        · linarith only [h3999, h4001, h4003, hlam]
                      · linarith only [h0, h3924, h4002, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2860, h3923, h4001, hc01, hlam, hphi, u1elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4045 | h4045
                · linarith only [h3923, h3924, h4045, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4047 | h4047
                  · linarith only [h3428, h3923, h4047, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4049 | h4049
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4050 | h4050
                      · linarith only [h3923, h3924, h4047, h4050, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4052 | h4052
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4053 | h4053
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4054 | h4054
                            · linarith only [h2860, h4045, h4049, h4050, h4053, h4054, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4056 | h4056
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4057 | h4057
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4058 | h4058
                                  · linarith only [h3923, h4054, h4058, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4060 | h4060
                                    · linarith only [h0, h4050, h4058, h4060, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · rcases h1bigk with h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c | h4062c
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h0, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h2428, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h2860, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h3180, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hc01, hlam, hphi, p4062_1, u1elo1]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4047, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h2860, h4050, h4058, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4062_1]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4050, hlam, p4062_1]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hc01, hlam, hphi, p4062_1, u1elo2]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h0, h3923, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4062_1, u1elo2]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h2860, hc01, hlam, hphi, p4062_1, u1elo2]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h3180, hc01, hlam, hphi, p4062_1, u1elo2]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4049, hc01, hlam, hphi, p4062_1, u1elo1]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4049, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4052, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4054, hlam, p4062_1]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hc01, hlam, hphi, p4062_1, u1elo4]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h0, hc01, hlam, hphi, p4062_1, u1elo4]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h4053, hlam, p4062_0]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [h2860, h4053, hc01, hlam, hphi, p4062_1, u1elo2]
                                      · obtain ⟨p4062_0, p4062_1, p4062_2, p4062_3⟩ := h4062c
                                        linarith only [hlam, p4062_0]
                                · linarith only [h3428, h3923, h4053, h4056, h4057, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · linarith only [h2860, h4047, h4049, h4056, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4090 | h4090
                            · linarith only [h2860, h4045, h4049, h4090, hc01, hlam, hphi, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4092 | h4092
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4093 | h4093
                                · linarith only [h0, h4047, h4053, h4093, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h2860, h4047, h4049, h4093, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h2860, h4047, h4049, h4092, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h4047, h4049, h4052, hlam]
                    · linarith only [h0, h3923, h4049, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h4099 | h4099
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4100 | h4100
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4101 | h4101
                  · linarith only [h3428, h4099, h4101, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4103 | h4103
                    · linarith only [h3923, h4099, h4101, h4103, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4105 | h4105
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4106 | h4106
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4107 | h4107
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4108 | h4108
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4109 | h4109
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4110 | h4110
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4111 | h4111
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4112 | h4112
                                    · rcases h1bigk with h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h0, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h2428, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h2860, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h3180, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4103, h4106, hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4101, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4103, hlam, p4113_1]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h3180, h4103, h4106, hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h0, hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h2860, hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h3180, hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hc01, hlam, hphi, p4113_1, u1elo3]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h3180, h4105, hc01, hlam, hphi, p4113_1, u1elo3]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4106, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h3180, h4106, hc01, hlam, hphi, p4113_1, u1elo2]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4105, hc01, hlam, hphi, p4113_1, u1elo1]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4105, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4107, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [h4108, hlam, p4113_0]
                                      · obtain ⟨p4113_0, p4113_1, p4113_2, p4113_3⟩ := h4113c
                                        linarith only [hlam, p4113_0]
                                    · rcases h1bigk with h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h0, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h2428, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h2860, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h3180, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4103, h4106, hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4101, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4103, hlam, p4139_1]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h3180, h4103, h4106, hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h0, hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h2860, hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h3180, hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hc01, hlam, hphi, p4139_1, u1elo3]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h0, h4099, hc25, hlam, hphi, ht01, ht0b, ht5b, p4139_1, u1elo3]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4106, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h3180, h4106, hc01, hlam, hphi, p4139_1, u1elo2]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4105, hc01, hlam, hphi, p4139_1, u1elo1]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4105, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4107, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [h4108, hlam, p4139_0]
                                      · obtain ⟨p4139_0, p4139_1, p4139_2, p4139_3⟩ := h4139c
                                        linarith only [hlam, p4139_0]
                                  · linarith only [h4100, h4103, h4111, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h3180, h4103, h4105, h4109, h4110, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h3180, h4101, h4105, h4109, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2860, h4099, h4100, h4108, hc01, hlam, hphi, u1elo1]
                          · linarith only [h4101, h4105, h4107, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4170 | h4170
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4171 | h4171
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4172 | h4172
                              · linarith only [h3180, h4101, h4105, h4106, h4172, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h3180, h4101, h4105, h4172, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h3180, h4100, h4101, h4105, h4106, h4171, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h4101, h4105, h4170, hlam]
                      · linarith only [h0, h4099, h4105, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3923, h4099, h4100, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4179 | h4179
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4180 | h4180
                  · linarith only [h0, h3428, h4180, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4182 | h4182
                    · linarith only [h0, h3923, h4180, h4182, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4184 | h4184
                      · linarith only [h0, h4099, h4180, h4184, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4186 | h4186
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4187 | h4187
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4188 | h4188
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4189 | h4189
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4190 | h4190
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4191 | h4191
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4192 | h4192
                                    · rcases h1bigk with h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h0, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h2428, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h2860, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h3180, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4184, h4186, h4188, hc01, hlam, hphi, p4193_1, u1elo2]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4180, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4182, hlam, p4193_1]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4184, hlam, p4193_1]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hc01, hlam, hphi, p4193_1, u1elo2]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h0, hc01, hlam, hphi, p4193_1, u1elo2]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h2860, hc01, hlam, hphi, p4193_1, u1elo2]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h0, h4184, hc01, hlam, hphi, p4193_1, u1elo2]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hc01, hlam, hphi, p4193_1, u1elo3]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h0, hc01, hlam, hphi, p4193_1, u1elo3]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4186, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h0, h4184, h4186, hc01, hlam, hphi, p4193_1, u1elo2]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hc01, hlam, hphi, p4193_1, u1elo4]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h0, hc01, hlam, hphi, p4193_1, u1elo4]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4187, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [h4188, hlam, p4193_0]
                                      · obtain ⟨p4193_0, p4193_1, p4193_2, p4193_3⟩ := h4193c
                                        linarith only [hlam, p4193_0]
                                    · rcases h1bigk with h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h0, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h2428, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h2860, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h3180, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hc01, hlam, hphi, p4219_1, u1elo1]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h4180, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h4182, hlam, p4219_1]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h4184, hlam, p4219_1]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hc01, hlam, hphi, p4219_1, u1elo2]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h0, hc01, hlam, hphi, p4219_1, u1elo2]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h2860, hc01, hlam, hphi, p4219_1, u1elo2]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h3180, hc01, hlam, hphi, p4219_1, u1elo2]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hc01, hlam, hphi, p4219_1, u1elo3]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h0, hc01, hlam, hphi, p4219_1, u1elo3]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h4186, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h0, h4184, h4186, hc01, hlam, hphi, p4219_1, u1elo2]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hc01, hlam, hphi, p4219_1, u1elo4]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h0, hc01, hlam, hphi, p4219_1, u1elo4]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h4187, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [h4188, hlam, p4219_0]
                                      · obtain ⟨p4219_0, p4219_1, p4219_2, p4219_3⟩ := h4219c
                                        linarith only [hlam, p4219_0]
                                  · linarith only [h0, h3923, h4179, h4191, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h4180, h4190, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h4180, h4189, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2860, h4179, h4188, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4249 | h4249
                            · linarith only [h4186, h4187, h4249, hlam]
                            · linarith only [h2860, h4179, h4249, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4252 | h4252
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4253 | h4253
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4254 | h4254
                              · linarith only [h2428, h4186, h4254, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h4180, h4254, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2860, h4179, h4253, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4258 | h4258
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4259 | h4259
                              · linarith only [h2428, h4186, h4259, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h4180, h4259, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2860, h4179, h4258, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4263 | h4263
                  · linarith only [h0, h3428, h4263, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4265 | h4265
                    · linarith only [h0, h3923, h4265, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4267 | h4267
                      · linarith only [h0, h4099, h4267, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4269 | h4269
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4270 | h4270
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4271 | h4271
                            · linarith only [h2860, h4179, h4269, h4271, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4273 | h4273
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4274 | h4274
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4275 | h4275
                                  · linarith only [h0, h4265, h4271, h4273, h4275, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h4265, h4275, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h3428, h4270, h4274, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h4263, h4269, h4273, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4280 | h4280
                            · linarith only [h0, h3923, h4179, h4280, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4282 | h4282
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4283 | h4283
                                · linarith only [h2428, h4270, h4283, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h4263, h4283, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h4263, h4269, h4282, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4287 | h4287
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4288 | h4288
                            · linarith only [h0, h3923, h4179, h4288, hc01, hlam, hphi, u1elo3]
                            · linarith only [h4269, h4287, h4288, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4291 | h4291
                            · linarith only [h0, h3923, h4179, h4291, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4293 | h4293
                              · linarith only [h2428, h4269, h4293, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h4263, h4293, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
