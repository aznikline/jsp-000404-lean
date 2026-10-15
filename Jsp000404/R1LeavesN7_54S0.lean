import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h5 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
  · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h11, h14, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h11, h13, h14, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h1, h13, h17, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · rcases h1bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h12, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h10, h11, h13, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h10, h11, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      rcases p19_3 (m.d 0 1) (by simp) with h24 | h24
                      · rcases p19_3 (m.d 1 2) (by simp) with h25 | h25
                        · linarith only [h0, h25, hlam]
                        · linarith only [h25, h7, hlam]
                      · linarith only [h24, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h0, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h10, h11, h13, h8, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h0, h10, h11, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h0, h10, h11, h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h1, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h5, hlam, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h10, h11, h13, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h1, h10, h11, h13, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p19_1, u3elo0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h2, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h6, hlam, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h8, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h1, h10, h11, h13, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p19_1, u3elo0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h3, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h7, hlam, p19_1]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h9, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [h10, hlam, p19_0]
                    · have p19_0 := h19c.1
                      have p19_1 := h19c.2.1
                      have p19_2 := h19c.2.2.1
                      have p19_3 := h19c.2.2.2
                      linarith only [hlam, p19_0]
              · linarith only [h12, h4, hc23, hlam, hphi, u3elo0]
            · linarith only [h1, h11, h8, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
            · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                · linarith only [h0, h10, h53, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h10, h51, h55, h6, hlam]
                  · rcases h1bigk with h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h5, h52, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h60 | h60
                      · rcases p57_3 (m.d 1 2) (by simp) with h61 | h61
                        · linarith only [h0, h61, hlam]
                        · linarith only [h5, h61, hlam]
                      · linarith only [h60, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h65 | h65
                      · rcases p57_3 (m.d 1 2) (by simp) with h66 | h66
                        · linarith only [h0, h66, hlam]
                        · linarith only [h6, h66, hlam]
                      · linarith only [h65, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h70 | h70
                      · rcases p57_3 (m.d 1 2) (by simp) with h71 | h71
                        · linarith only [h0, h71, hlam]
                        · linarith only [h7, h71, hlam]
                      · linarith only [h70, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h0, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h0, h5, h52, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h78 | h78
                      · rcases p57_3 (m.d 1 2) (by simp) with h79 | h79
                        · rcases p57_3 (m.d 1 3) (by simp) with h80 | h80
                          · linarith only [h5, h80, hlam]
                          · linarith only [h8, h80, hlam]
                        · linarith only [h6, h79, hlam]
                      · linarith only [h2, h78, hlam]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h85 | h85
                      · rcases p57_3 (m.d 1 2) (by simp) with h86 | h86
                        · rcases p57_3 (m.d 1 3) (by simp) with h87 | h87
                          · linarith only [h5, h87, hlam]
                          · linarith only [h87, h9, hlam]
                        · linarith only [h7, h86, hlam]
                      · linarith only [h3, h85, hlam]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h1, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h5, hlam, p57_1]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h95 | h95
                      · rcases p57_3 (m.d 1 2) (by simp) with h96 | h96
                        · rcases p57_3 (m.d 1 3) (by simp) with h97 | h97
                          · rcases p57_3 (m.d 1 4) (by simp) with h98 | h98
                            · linarith only [h8, h98, hlam]
                            · rcases p57_3 (m.d 1 5) (by simp) with h100 | h100
                              · linarith only [h100, h9, hlam]
                              · linarith only [h10, h100, hlam]
                          · linarith only [h8, h97, hlam]
                        · linarith only [h6, h96, hlam]
                      · linarith only [h2, h95, hlam]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h106 | h106
                      · rcases p57_3 (m.d 1 2) (by simp) with h107 | h107
                        · rcases p57_3 (m.d 1 3) (by simp) with h108 | h108
                          · rcases p57_3 (m.d 1 4) (by simp) with h109 | h109
                            · linarith only [h109, h8, hlam]
                            · rcases p57_3 (m.d 1 5) (by simp) with h111 | h111
                              · linarith only [h111, h9, hlam]
                              · rcases h1emin with h113 | h113 | h113 | h113 | h113
                                · rcases h3bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hc13, hlam, hphi, p114_1, u3elo0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h52, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p114_1, u3elo0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    rcases p114_3 (m.d 0 3) (by simp) with h118 | h118
                                    · rcases p114_3 (m.d 1 3) (by simp) with h119 | h119
                                      · linarith only [h1, h119, hlam]
                                      · linarith only [h119, h8, hlam]
                                    · linarith only [h118, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    rcases p114_3 (m.d 0 3) (by simp) with h123 | h123
                                    · rcases p114_3 (m.d 1 3) (by simp) with h124 | h124
                                      · linarith only [h1, h124, hlam]
                                      · linarith only [h124, h9, hlam]
                                    · linarith only [h123, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h52, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p114_1, u3elo1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    rcases p114_3 (m.d 0 3) (by simp) with h131 | h131
                                    · rcases p114_3 (m.d 1 3) (by simp) with h132 | h132
                                      · rcases p114_3 (m.d 2 3) (by simp) with h133 | h133
                                        · linarith only [h133, h5, hlam]
                                        · linarith only [h133, h51, hlam]
                                      · linarith only [h132, hlam, p114_0]
                                    · linarith only [h10, h131, h3, h4, h51, h6, hlam]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    rcases p114_3 (m.d 0 3) (by simp) with h138 | h138
                                    · rcases p114_3 (m.d 1 3) (by simp) with h139 | h139
                                      · rcases p114_3 (m.d 2 3) (by simp) with h140 | h140
                                        · linarith only [h140, h5, hlam]
                                        · linarith only [h140, h52, hlam]
                                      · linarith only [h139, hlam, p114_0]
                                    · linarith only [h138, h4, hlam]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, h10, h51, h6, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p114_1, p57_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h5, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h0, h5, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, h10, h51, h6, hlam, p114_1, p57_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h8, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h51, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h55, hlam, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h4, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h9, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h52, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p114_1, u3elo0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                · rcases h3bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hc13, hlam, hphi, p160_1, u3elo0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h52, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p160_1, u3elo0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 3) (by simp) with h164 | h164
                                    · rcases p160_3 (m.d 1 3) (by simp) with h165 | h165
                                      · linarith only [h1, h165, hlam]
                                      · linarith only [h165, h8, hlam]
                                    · linarith only [h164, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 3) (by simp) with h169 | h169
                                    · rcases p160_3 (m.d 1 3) (by simp) with h170 | h170
                                      · linarith only [h1, h170, hlam]
                                      · linarith only [h170, h9, hlam]
                                    · linarith only [h169, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h1, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h52, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p160_1, u3elo1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 3) (by simp) with h177 | h177
                                    · rcases p160_3 (m.d 1 3) (by simp) with h178 | h178
                                      · rcases p160_3 (m.d 2 3) (by simp) with h179 | h179
                                        · linarith only [h179, h5, hlam]
                                        · linarith only [h179, h51, hlam]
                                      · linarith only [h178, hlam, p160_0]
                                    · linarith only [h177, h4, h55, hlam]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 3) (by simp) with h184 | h184
                                    · rcases p160_3 (m.d 1 3) (by simp) with h185 | h185
                                      · rcases p160_3 (m.d 2 3) (by simp) with h186 | h186
                                        · linarith only [h186, h5, hlam]
                                        · linarith only [h186, h52, hlam]
                                      · linarith only [h185, hlam, p160_0]
                                    · linarith only [h184, h4, hlam]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h1, h10, h51, h6, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, p57_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h5, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p160_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h5, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p160_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h1, h10, h51, h6, hlam, p160_1, p57_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h8, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h51, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h55, hlam, p160_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h4, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h9, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h52, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p160_1, u3elo0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                · linarith only [h113, hlam, ht12, ht23, u3elo1]
                                · linarith only [h10, h113, hc45, hlam, ht12, ht23, ht34]
                                · linarith only [h113, h3, h4, hlam, ht12, ht23, u3elo0]
                          · linarith only [h108, h9, hlam]
                        · linarith only [h107, h7, hlam]
                      · linarith only [h106, h3, hlam]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h2, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h6, hlam, p57_1]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h8, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h10, hlam, p57_1]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h3, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h7, hlam, p57_1]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [h9, hlam, p57_0]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      rcases p57_3 (m.d 0 1) (by simp) with h220 | h220
                      · rcases p57_3 (m.d 1 2) (by simp) with h221 | h221
                        · rcases p57_3 (m.d 1 3) (by simp) with h222 | h222
                          · rcases p57_3 (m.d 1 4) (by simp) with h223 | h223
                            · linarith only [h10, h223, hlam]
                            · rcases p57_3 (m.d 1 5) (by simp) with h225 | h225
                              · rcases h1emin with h226 | h226 | h226 | h226 | h226
                                · rcases h3bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hc13, hlam, hphi, p227_1, u3elo0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hc23, hlam, hphi, p227_1, u3elo0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    rcases p227_3 (m.d 0 3) (by simp) with h231 | h231
                                    · rcases p227_3 (m.d 1 3) (by simp) with h232 | h232
                                      · linarith only [h1, h232, hlam]
                                      · linarith only [h232, h8, hlam]
                                    · linarith only [h231, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    rcases p227_3 (m.d 0 3) (by simp) with h236 | h236
                                    · rcases p227_3 (m.d 1 3) (by simp) with h237 | h237
                                      · linarith only [h1, h237, hlam]
                                      · linarith only [h237, h9, hlam]
                                    · linarith only [h236, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h1, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h52, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p227_1, u3elo1]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    rcases p227_3 (m.d 0 3) (by simp) with h244 | h244
                                    · rcases p227_3 (m.d 1 3) (by simp) with h245 | h245
                                      · rcases p227_3 (m.d 2 3) (by simp) with h246 | h246
                                        · linarith only [h246, h5, hlam]
                                        · linarith only [h246, h51, hlam]
                                      · linarith only [h245, hlam, p227_0]
                                    · linarith only [h244, h3, h4, h52, h55, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo2]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    rcases p227_3 (m.d 0 3) (by simp) with h251 | h251
                                    · rcases p227_3 (m.d 1 3) (by simp) with h252 | h252
                                      · rcases p227_3 (m.d 2 3) (by simp) with h253 | h253
                                        · linarith only [h253, h5, hlam]
                                        · linarith only [h253, h52, hlam]
                                      · linarith only [h252, hlam, p227_0]
                                    · linarith only [h251, h4, hlam]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h0, h3, h4, h5, h51, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1, p57_1]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h5, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h0, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p227_1]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h3, h4, h51, h6, hlam, p227_1, p57_1]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h8, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h51, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h55, hlam, p227_1]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h4, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h9, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h52, hlam, p227_0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p227_1, u3elo0]
                                  · have p227_0 := h227c.1
                                    have p227_1 := h227c.2.1
                                    have p227_2 := h227c.2.2.1
                                    have p227_3 := h227c.2.2.2
                                    linarith only [hlam, p227_0]
                                · rcases h3bigk with h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hc13, hlam, hphi, p273_1, u3elo0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hc23, hlam, hphi, p273_1, u3elo0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    rcases p273_3 (m.d 0 3) (by simp) with h277 | h277
                                    · rcases p273_3 (m.d 1 3) (by simp) with h278 | h278
                                      · linarith only [h1, h278, hlam]
                                      · linarith only [h278, h8, hlam]
                                    · linarith only [h277, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    rcases p273_3 (m.d 0 3) (by simp) with h282 | h282
                                    · rcases p273_3 (m.d 1 3) (by simp) with h283 | h283
                                      · linarith only [h1, h283, hlam]
                                      · linarith only [h283, h9, hlam]
                                    · linarith only [h282, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h1, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h52, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo1]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    rcases p273_3 (m.d 0 3) (by simp) with h290 | h290
                                    · rcases p273_3 (m.d 1 3) (by simp) with h291 | h291
                                      · rcases p273_3 (m.d 2 3) (by simp) with h292 | h292
                                        · linarith only [h292, h5, hlam]
                                        · linarith only [h292, h51, hlam]
                                      · linarith only [h291, hlam, p273_0]
                                    · linarith only [h290, h4, h55, hlam]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    rcases p273_3 (m.d 0 3) (by simp) with h297 | h297
                                    · rcases p273_3 (m.d 1 3) (by simp) with h298 | h298
                                      · rcases p273_3 (m.d 2 3) (by simp) with h299 | h299
                                        · linarith only [h299, h5, hlam]
                                        · linarith only [h299, h52, hlam]
                                      · linarith only [h298, hlam, p273_0]
                                    · linarith only [h297, h4, hlam]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h3, h4, h51, h6, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p273_1, p57_1]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h5, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p273_1]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h0, h5, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p273_1]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h3, h4, h51, h6, hlam, p273_1, p57_1]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h8, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h51, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h55, hlam, p273_1]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h4, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h9, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h52, hlam, p273_0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo0]
                                  · have p273_0 := h273c.1
                                    have p273_1 := h273c.2.1
                                    have p273_2 := h273c.2.2.1
                                    have p273_3 := h273c.2.2.2
                                    linarith only [hlam, p273_0]
                                · linarith only [h226, hlam, ht12, ht23, u3elo1]
                                · linarith only [h226, h3, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p57_1]
                                · linarith only [h226, h3, h4, hlam, ht12, ht23, u3elo0]
                              · linarith only [h10, h225, hlam]
                          · linarith only [h222, h8, hlam]
                        · linarith only [h221, h6, hlam]
                      · linarith only [h2, h220, hlam]
                    · have p57_0 := h57c.1
                      have p57_1 := h57c.2.1
                      have p57_2 := h57c.2.2.1
                      have p57_3 := h57c.2.2.2
                      linarith only [hlam, p57_0]
              · linarith only [h1, h52, h9, hc23, hlam, hphi, u3elo0]
            · linarith only [h1, h51, h8, hc23, hlam, hphi, u3elo0]
        · linarith only [h4, h9, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
        · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
          · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
            · linarith only [h330, h332, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
              · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                · rcases m.htr 3 4 5 (by decide) (by decide) with h336 | h336
                  · rcases h1bigk with h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h334, h336, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      rcases p337_3 (m.d 0 1) (by simp) with h340 | h340
                      · rcases p337_3 (m.d 1 2) (by simp) with h341 | h341
                        · linarith only [h0, h341, hlam]
                        · linarith only [h341, h5, hlam]
                      · linarith only [h340, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      rcases p337_3 (m.d 0 1) (by simp) with h345 | h345
                      · rcases p337_3 (m.d 1 2) (by simp) with h346 | h346
                        · linarith only [h0, h346, hlam]
                        · linarith only [h346, h6, hlam]
                      · linarith only [h345, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      rcases p337_3 (m.d 0 1) (by simp) with h350 | h350
                      · rcases p337_3 (m.d 1 2) (by simp) with h351 | h351
                        · linarith only [h0, h351, hlam]
                        · linarith only [h351, h7, hlam]
                      · linarith only [h350, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h0, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h0, h334, h336, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h0, h334, h336, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      rcases p337_3 (m.d 0 1) (by simp) with h359 | h359
                      · rcases p337_3 (m.d 1 2) (by simp) with h360 | h360
                        · rcases p337_3 (m.d 1 3) (by simp) with h361 | h361
                          · linarith only [h361, h5, hlam]
                          · linarith only [h330, h361, hlam]
                        · linarith only [h360, h7, hlam]
                      · linarith only [h3, h359, hlam]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h1, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h5, hlam, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h8, hlam, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h7, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p337_1, u3elo3]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h2, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h6, hlam, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h8, hc13, hlam, hphi, p337_1, u3elo3]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      rcases p337_3 (m.d 0 1) (by simp) with h375 | h375
                      · rcases p337_3 (m.d 1 2) (by simp) with h376 | h376
                        · rcases p337_3 (m.d 1 3) (by simp) with h377 | h377
                          · linarith only [h377, h8, hlam]
                          · linarith only [h330, h377, hlam]
                        · linarith only [h376, h7, hlam]
                      · linarith only [h3, h375, hlam]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h3, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h7, hlam, p337_1]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h330, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [h331, hlam, p337_0]
                    · have p337_0 := h337c.1
                      have p337_1 := h337c.2.1
                      have p337_2 := h337c.2.2.1
                      have p337_3 := h337c.2.2.2
                      linarith only [hlam, p337_0]
                  · linarith only [h331, h334, h336, h5, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h330, h331, h332, h334, h335, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h334, h4, hc23, hlam, hphi, u3elo0]
          · linarith only [h330, h331, h8, hlam]
        · linarith only [h330, h4, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
      · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
        · linarith only [h393, h5, h7, hlam]
        · linarith only [h393, h4, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h396 | h396
        · linarith only [h392, h396, h5, h7, hc23, hlam, hphi, u3elo3]
        · linarith only [h396, h4, hc13, hlam, hphi, u3elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
    · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
      · linarith only [h400, h5, h6, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
        · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
          · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
            · linarith only [h400, h404, h5, h6, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h404, h5, h6, hc23, hlam, hphi, u3elo3]
          · linarith only [h402, h403, h5, h6, hlam]
        · linarith only [h4, h402, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
      · linarith only [h409, h5, h6, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
        · linarith only [h399, h411, h5, hlam]
        · linarith only [h4, h411, hc13, hlam, hphi, u3elo0]

end R2N4
