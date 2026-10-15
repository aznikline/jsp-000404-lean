import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h10, h14, h17, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h17, h9, hc34, hlam, hphi, u4elo0]
                        · linarith only [h13, h16, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h14, h15, h8, h9, hc34, hlam, hphi, u4elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                          · rcases h0bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h22, h24, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h22, h24, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h14, h22, h24, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 1) (by simp) with h30 | h30
                              · rcases p25_3 (m.d 0 2) (by simp) with h31 | h31
                                · linarith only [h0, h31, hlam]
                                · linarith only [h31, h6, hlam]
                              · linarith only [h3, h30, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h14, h22, h24, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h14, h22, h24, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 1) (by simp) with h39 | h39
                              · rcases p25_3 (m.d 0 2) (by simp) with h40 | h40
                                · rcases p25_3 (m.d 0 3) (by simp) with h41 | h41
                                  · linarith only [h4, h41, hlam]
                                  · linarith only [h41, h8, hlam]
                                · linarith only [h40, h6, hlam]
                              · linarith only [h3, h39, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h1, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h4, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h14, h22, h24, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 1) (by simp) with h50 | h50
                              · rcases p25_3 (m.d 0 2) (by simp) with h51 | h51
                                · rcases p25_3 (m.d 0 3) (by simp) with h52 | h52
                                  · rcases p25_3 (m.d 0 4) (by simp) with h53 | h53
                                    · linarith only [h53, h7, hlam]
                                    · linarith only [h53, h9, hlam]
                                  · linarith only [h52, h8, hlam]
                                · linarith only [h51, h6, hlam]
                              · linarith only [h3, h50, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h2, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h5, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h7, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p25_1, u4elo0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h3, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h6, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h8, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h9, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                          · linarith only [h14, h24, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h23, h9, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                          · rcases h0bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h5, h71, hc01, hc45, hlam, hphi, ht0b, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h22, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h0, hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h14, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h0, h14, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h0, h22, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h1, hlam, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h4, hlam, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h14, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h0, h22, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h2, hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h5, hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h7, hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p73_1, u4elo0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h3, hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h6, hlam, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h8, hlam, p73_0]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [h9, hlam, p73_1]
                            · have p73_0 := h73c.1
                              have p73_1 := h73c.2.1
                              have p73_2 := h73c.2.2.1
                              have p73_3 := h73c.2.2.2
                              linarith only [hlam, p73_0]
                          · linarith only [h11, h14, h71, h72, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h71, h9, hc24, hlam, hphi, u4elo0]
                  · linarith only [h13, h9, hc14, hlam, hphi, u4elo0]
                · linarith only [h10, h12, h6, h9, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h10, h104, h109, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h106, h109, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h10, h105, h108, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h10, h104, h107, hc24, hlam, hphi, u4elo3]
                  · linarith only [h106, h9, hc14, hlam, hphi, u4elo0]
                · linarith only [h104, h105, h6, h9, hc24, hlam, hphi, u4elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                          · rcases h0bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h0, h116, h119, h121, hc01, hc45, hlam, hphi, ht0b, ht5b, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h1, h10, h116, h119, h121, hc01, hc45, hlam, hphi, ht0b, ht5b, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h104, h116, h119, h121, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              rcases p122_3 (m.d 0 1) (by simp) with h127 | h127
                              · rcases p122_3 (m.d 0 2) (by simp) with h128 | h128
                                · linarith only [h0, h128, hlam]
                                · linarith only [h128, h6, hlam]
                              · linarith only [h127, h3, hlam]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h0, hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h104, h116, h118, h119, h121, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h0, h104, h116, h119, h121, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              rcases p122_3 (m.d 0 1) (by simp) with h136 | h136
                              · rcases p122_3 (m.d 0 2) (by simp) with h137 | h137
                                · rcases p122_3 (m.d 0 3) (by simp) with h138 | h138
                                  · linarith only [h138, h4, hlam]
                                  · linarith only [h138, h8, hlam]
                                · linarith only [h137, h6, hlam]
                              · linarith only [h136, h3, hlam]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h1, hlam, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h4, hlam, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h104, h116, h119, h121, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              rcases p122_3 (m.d 0 1) (by simp) with h147 | h147
                              · rcases p122_3 (m.d 0 2) (by simp) with h148 | h148
                                · rcases p122_3 (m.d 0 3) (by simp) with h149 | h149
                                  · rcases p122_3 (m.d 0 4) (by simp) with h150 | h150
                                    · linarith only [h150, h7, hlam]
                                    · linarith only [h150, h9, hlam]
                                  · linarith only [h149, h8, hlam]
                                · linarith only [h148, h6, hlam]
                              · linarith only [h147, h3, hlam]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h2, hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h5, hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h7, hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p122_1, u4elo0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h3, hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h6, hlam, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h8, hlam, p122_0]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [h9, hlam, p122_1]
                            · have p122_0 := h122c.1
                              have p122_1 := h122c.2.1
                              have p122_2 := h122c.2.2.1
                              have p122_3 := h122c.2.2.2
                              linarith only [hlam, p122_0]
                          · linarith only [h121, h9, hc34, hlam, hphi, u4elo0]
                        · linarith only [h104, h120, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h104, h116, h118, h119, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h10, h116, h118, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                  · linarith only [h104, h116, h117, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                          · rcases h0bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h116, h172, h174, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h116, h172, h174, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h171, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h116, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h0, hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h116, h172, h174, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h0, h116, h174, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h0, h116, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h1, hlam, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h4, hlam, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h116, h174, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h0, h116, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h2, hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h5, hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h7, hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h116, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h3, hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h6, hlam, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h8, hlam, p176_0]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [h9, hlam, p176_1]
                            · have p176_0 := h176c.1
                              have p176_1 := h176c.2.1
                              have p176_2 := h176c.2.2.1
                              have p176_3 := h176c.2.2.2
                              linarith only [hlam, p176_0]
                          · linarith only [h171, h175, hc34, hlam, hphi, u4elo1]
                        · linarith only [h171, h174, hc24, hlam, hphi, u4elo1]
                      · linarith only [h10, h173, h8, h9, hc12, hlam, hphi, ht23, ht34, u4elo0]
                    · linarith only [h10, h172, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h171, h9, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
            · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
              · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                  · linarith only [h210, h9, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                        · linarith only [h2, h208, h214, h9, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                          · linarith only [h2, h208, h212, h216, h9, hlam]
                          · rcases h0bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h207, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 1) (by simp) with h222 | h222
                              · rcases p218_3 (m.d 0 2) (by simp) with h223 | h223
                                · linarith only [h0, h223, hlam]
                                · linarith only [h223, h5, hlam]
                              · linarith only [h2, h222, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 1) (by simp) with h227 | h227
                              · rcases p218_3 (m.d 0 2) (by simp) with h228 | h228
                                · linarith only [h0, h228, hlam]
                                · linarith only [h228, h6, hlam]
                              · linarith only [h227, h3, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h1, h207, h213, h216, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 1) (by simp) with h235 | h235
                              · rcases p218_3 (m.d 0 2) (by simp) with h236 | h236
                                · rcases p218_3 (m.d 0 3) (by simp) with h237 | h237
                                  · linarith only [h237, h4, hlam]
                                  · linarith only [h237, h7, hlam]
                                · linarith only [h236, h5, hlam]
                              · linarith only [h2, h235, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 1) (by simp) with h242 | h242
                              · rcases p218_3 (m.d 0 2) (by simp) with h243 | h243
                                · rcases p218_3 (m.d 0 3) (by simp) with h244 | h244
                                  · linarith only [h244, h4, hlam]
                                  · linarith only [h244, h8, hlam]
                                · linarith only [h243, h6, hlam]
                              · linarith only [h242, h3, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h1, hlam, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h4, hlam, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 1) (by simp) with h252 | h252
                              · rcases p218_3 (m.d 0 2) (by simp) with h253 | h253
                                · rcases p218_3 (m.d 0 3) (by simp) with h254 | h254
                                  · rcases p218_3 (m.d 0 4) (by simp) with h255 | h255
                                    · linarith only [h255, h7, hlam]
                                    · rcases p218_3 (m.d 0 5) (by simp) with h257 | h257
                                      · linarith only [h257, h8, hlam]
                                      · linarith only [h257, h9, hlam]
                                  · linarith only [h254, h7, hlam]
                                · linarith only [h253, h5, hlam]
                              · linarith only [h2, h252, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 1) (by simp) with h263 | h263
                              · rcases p218_3 (m.d 0 2) (by simp) with h264 | h264
                                · rcases p218_3 (m.d 0 3) (by simp) with h265 | h265
                                  · rcases p218_3 (m.d 0 4) (by simp) with h266 | h266
                                    · linarith only [h266, h7, hlam]
                                    · rcases p218_3 (m.d 0 5) (by simp) with h268 | h268
                                      · linarith only [h268, h8, hlam]
                                      · rcases h2bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h207, h213, h216, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          rcases p270_3 (m.d 0 2) (by simp) with h273 | h273
                                          · rcases p270_3 (m.d 1 2) (by simp) with h274 | h274
                                            · linarith only [h0, h274, hlam]
                                            · linarith only [h207, h274, hlam]
                                          · linarith only [h273, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h2, h208, h4, h9, hlam, p218_1, p270_2]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h209, h3, h4, hlam, p218_1, p270_2]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h213, h216, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          rcases p270_3 (m.d 0 2) (by simp) with h283 | h283
                                          · rcases p270_3 (m.d 1 2) (by simp) with h284 | h284
                                            · rcases p270_3 (m.d 2 3) (by simp) with h285 | h285
                                              · linarith only [h207, h285, hlam]
                                              · linarith only [h212, h285, hlam]
                                            · linarith only [h284, hlam, p270_0]
                                          · linarith only [h283, h5, hlam]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          rcases p270_3 (m.d 0 2) (by simp) with h290 | h290
                                          · rcases p270_3 (m.d 1 2) (by simp) with h291 | h291
                                            · rcases p270_3 (m.d 2 3) (by simp) with h292 | h292
                                              · linarith only [h207, h292, hlam]
                                              · linarith only [h213, h292, hlam]
                                            · linarith only [h291, hlam, p270_0]
                                          · linarith only [h290, h6, hlam]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h4, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h207, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h207, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h207, hc01, hc25, hlam, hphi, ht0b, ht5b, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h5, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h208, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h212, hlam, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h214, hlam, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h6, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h209, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h213, hlam, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h212, h4, h6, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p218_1, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                  · linarith only [h265, h8, hlam]
                                · linarith only [h264, h6, hlam]
                              · linarith only [h263, h3, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h2, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h5, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h7, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h9, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h3, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h6, hlam, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h8, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h2, h9, hc14, hlam, hphi, p218_1, u4elo4]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                      · linarith only [h212, h213, h8, h9, hc34, hlam, hphi, u4elo4]
                    · linarith only [h212, h7, h9, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h207, h209, h6, h9, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h207, h208, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                  · linarith only [h2, h331, h9, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                        · linarith only [h2, h207, h329, h335, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                          · linarith only [h2, h329, h333, h337, h9, hlam]
                          · rcases h0bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h207, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h207, h330, h334, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h343 | h343
                              · rcases p339_3 (m.d 0 2) (by simp) with h344 | h344
                                · linarith only [h0, h344, hlam]
                                · linarith only [h344, h5, hlam]
                              · linarith only [h2, h343, hlam]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h348 | h348
                              · rcases p339_3 (m.d 0 2) (by simp) with h349 | h349
                                · linarith only [h0, h349, hlam]
                                · linarith only [h349, h6, hlam]
                              · linarith only [h3, h348, hlam]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h0, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h207, h330, h333, h335, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h356 | h356
                              · rcases p339_3 (m.d 0 2) (by simp) with h357 | h357
                                · rcases p339_3 (m.d 0 3) (by simp) with h358 | h358
                                  · linarith only [h358, h4, hlam]
                                  · linarith only [h358, h7, hlam]
                                · linarith only [h357, h5, hlam]
                              · linarith only [h2, h356, hlam]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h363 | h363
                              · rcases p339_3 (m.d 0 2) (by simp) with h364 | h364
                                · rcases p339_3 (m.d 0 3) (by simp) with h365 | h365
                                  · linarith only [h365, h4, hlam]
                                  · linarith only [h365, h8, hlam]
                                · linarith only [h364, h6, hlam]
                              · linarith only [h3, h363, hlam]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h1, hlam, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h4, hlam, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h373 | h373
                              · rcases p339_3 (m.d 0 2) (by simp) with h374 | h374
                                · rcases p339_3 (m.d 0 3) (by simp) with h375 | h375
                                  · rcases p339_3 (m.d 0 4) (by simp) with h376 | h376
                                    · linarith only [h376, h7, hlam]
                                    · rcases p339_3 (m.d 0 5) (by simp) with h378 | h378
                                      · linarith only [h378, h8, hlam]
                                      · linarith only [h378, h9, hlam]
                                  · linarith only [h375, h7, hlam]
                                · linarith only [h374, h5, hlam]
                              · linarith only [h2, h373, hlam]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h384 | h384
                              · rcases p339_3 (m.d 0 2) (by simp) with h385 | h385
                                · rcases p339_3 (m.d 0 3) (by simp) with h386 | h386
                                  · rcases p339_3 (m.d 0 4) (by simp) with h387 | h387
                                    · linarith only [h387, h7, hlam]
                                    · rcases p339_3 (m.d 0 5) (by simp) with h389 | h389
                                      · linarith only [h389, h8, hlam]
                                      · rcases h2bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          rcases p391_3 (m.d 0 2) (by simp) with h393 | h393
                                          · rcases p391_3 (m.d 1 2) (by simp) with h394 | h394
                                            · linarith only [h0, h394, hlam]
                                            · rcases p391_3 (m.d 2 3) (by simp) with h396 | h396
                                              · linarith only [h396, h4, hlam]
                                              · linarith only [h207, h396, hlam]
                                          · linarith only [h0, h393, hlam]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h0, h207, h330, h333, h335, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h207, h330, h335, h4, hlam, p391_2]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h207, h330, h4, hlam, p391_2]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h0, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h207, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h207, h333, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h0, h207, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h4, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h0, h329, h333, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          rcases p391_3 (m.d 0 2) (by simp) with h411 | h411
                                          · rcases p391_3 (m.d 1 2) (by simp) with h412 | h412
                                            · linarith only [h207, h412, hlam]
                                            · linarith only [h329, h412, hlam]
                                          · linarith only [h411, h5, hlam]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          rcases p391_3 (m.d 0 2) (by simp) with h416 | h416
                                          · rcases p391_3 (m.d 1 2) (by simp) with h417 | h417
                                            · linarith only [h207, h417, hlam]
                                            · linarith only [h330, h417, hlam]
                                          · linarith only [h416, h6, hlam]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h5, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h329, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h333, hlam, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h335, hlam, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h6, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h330, hlam, p391_0]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h334, hlam, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [h0, h330, h333, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p391_1]
                                        · have p391_0 := h391c.1
                                          have p391_1 := h391c.2.1
                                          have p391_2 := h391c.2.2.1
                                          have p391_3 := h391c.2.2.2
                                          linarith only [hlam, p391_0]
                                  · linarith only [h386, h8, hlam]
                                · linarith only [h385, h6, hlam]
                              · linarith only [h3, h384, hlam]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h2, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h5, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h7, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h9, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h3, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h6, hlam, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h8, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h2, h329, h333, h9, hc34, hlam, hphi, p339_1, u4elo4]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                      · linarith only [h0, h207, h330, h334, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h207, h329, h333, hc24, hlam, hphi, u4elo3]
                · linarith only [h329, h330, h6, h9, hc24, hlam, hphi, u4elo4]
              · linarith only [h329, h5, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h448 | h448
          · linarith only [h448, h7, h8, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
            · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
              · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
                · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                  · linarith only [h2, h448, h453, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                      · linarith only [h0, h450, h456, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                        · linarith only [h2, h448, h451, h458, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                          · linarith only [h1, h448, h450, h455, h460, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h460, h7, h8, hc34, hlam, hphi, u4elo4]
                    · linarith only [h455, h7, h8, hc23, hc35, hlam, hphi]
                · linarith only [h448, h450, h452, h6, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h450, h451, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h466 | h466
              · linarith only [h4, h448, h450, h466, h8, hc24, hlam, hphi, u4elo4]
              · linarith only [h448, h466, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
        · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
          · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
            · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
              · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                    · linarith only [h1, h471, h475, h7, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                          · rcases h0bigk with h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h0, h472, h475, h477, h479, hc01, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h1, h471, h477, h479, hc01, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h1, h471, h477, h479, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              rcases p480_3 (m.d 0 1) (by simp) with h485 | h485
                              · rcases p480_3 (m.d 0 2) (by simp) with h486 | h486
                                · linarith only [h0, h486, hlam]
                                · linarith only [h486, h6, hlam]
                              · linarith only [h3, h485, hlam]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h0, hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h1, h471, h477, h479, hc02, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h0, h1, h471, h477, h479, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              rcases p480_3 (m.d 0 1) (by simp) with h494 | h494
                              · rcases p480_3 (m.d 0 2) (by simp) with h495 | h495
                                · rcases p480_3 (m.d 0 3) (by simp) with h496 | h496
                                  · linarith only [h4, h496, hlam]
                                  · linarith only [h469, h496, hlam]
                                · linarith only [h495, h6, hlam]
                              · linarith only [h3, h494, hlam]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h1, hlam, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h4, hlam, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h7, hlam, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p480_1, u4elo3]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h2, hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h5, hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h1, h471, h477, hc04, hc35, hlam, hphi, ht0b, ht5b, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h3, h473, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p480_1, u4elo3]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h3, hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h6, hlam, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h469, hlam, p480_0]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [h470, hlam, p480_1]
                            · have p480_0 := h480c.1
                              have p480_1 := h480c.2.1
                              have p480_2 := h480c.2.2.1
                              have p480_3 := h480c.2.2.2
                              linarith only [hlam, p480_0]
                          · linarith only [h479, h7, hc03, hlam, hphi, ht34, u4elo4]
                        · linarith only [h470, h475, h477, h478, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                      · linarith only [h469, h477, h7, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h470, h474, h7, hc14, hlam, hphi, u4elo3]
                · linarith only [h469, h471, h473, h6, h7, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h471, h472, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h471, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h469, h470, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h524 | h524
          · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
            · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
              · rcases m.htr 1 2 5 (by decide) (by decide) with h527 | h527
                · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                    · linarith only [h0, h2, h525, h528, h529, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                      · linarith only [h1, h469, h525, h531, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                          · rcases h0bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h0, h526, h533, hc01, hc45, hlam, hphi, ht0b, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              rcases p535_3 (m.d 0 1) (by simp) with h538 | h538
                              · rcases p535_3 (m.d 0 2) (by simp) with h539 | h539
                                · linarith only [h0, h539, hlam]
                                · linarith only [h4, h539, hlam]
                              · linarith only [h1, h538, hlam]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h2, h526, h533, hc01, hc45, hlam, hphi, ht0b, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              rcases p535_3 (m.d 0 1) (by simp) with h544 | h544
                              · rcases p535_3 (m.d 0 2) (by simp) with h545 | h545
                                · linarith only [h0, h545, hlam]
                                · linarith only [h545, h6, hlam]
                              · linarith only [h3, h544, hlam]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h0, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              rcases p535_3 (m.d 0 1) (by simp) with h551 | h551
                              · rcases p535_3 (m.d 0 2) (by simp) with h552 | h552
                                · rcases p535_3 (m.d 0 3) (by simp) with h553 | h553
                                  · linarith only [h4, h553, hlam]
                                  · rcases p535_3 (m.d 0 4) (by simp) with h555 | h555
                                    · linarith only [h5, h555, hlam]
                                    · linarith only [h555, h7, hlam]
                                · linarith only [h4, h552, hlam]
                              · linarith only [h1, h551, hlam]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h2, h526, h533, hc02, hc45, hlam, hphi, ht0b, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              rcases p535_3 (m.d 0 1) (by simp) with h561 | h561
                              · rcases p535_3 (m.d 0 2) (by simp) with h562 | h562
                                · rcases p535_3 (m.d 0 3) (by simp) with h563 | h563
                                  · linarith only [h4, h563, hlam]
                                  · rcases p535_3 (m.d 0 4) (by simp) with h565 | h565
                                    · linarith only [h5, h565, hlam]
                                    · linarith only [h524, h565, hlam]
                                · linarith only [h562, h6, hlam]
                              · linarith only [h3, h561, hlam]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h4, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h7, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h469, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h2, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h5, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, h525, hc23, hlam, hphi, ht34, p535_1, u4elo0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, h469, h525, h7, hc23, hlam, hphi, ht34, p535_1, u4elo3]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h3, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h6, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, h469, h525, hc23, hc35, hlam, hphi, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h524, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                          · linarith only [h526, h533, h534, h7, hc04, hlam, hphi, u4elo1]
                        · linarith only [h2, h528, h533, hc24, hlam, hphi, u4elo0]
                  · linarith only [h524, h528, h7, hc14, hlam, hphi, u4elo3]
                · linarith only [h524, h525, h527, h6, h7, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h525, h526, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h525, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h591 | h591
            · rcases m.htr 1 2 4 (by decide) (by decide) with h592 | h592
              · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
                · rcases m.htr 1 4 5 (by decide) (by decide) with h594 | h594
                  · linarith only [h524, h594, h7, hc03, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h596 | h596
                    · linarith only [h1, h524, h591, h596, h7, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
                      · linarith only [h1, h469, h591, h598, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h600 | h600
                        · linarith only [h1, h524, h591, h600, h7, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h602 | h602
                          · linarith only [h1, h524, h591, h602, h7, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h1, h591, h602, h7, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h524, h591, h593, h6, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h591, h592, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h591, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h608 | h608
      · rcases m.htr 0 3 5 (by decide) (by decide) with h609 | h609
        · linarith only [h4, h6, h609, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
          · linarith only [h4, h6, h608, h611, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h613 | h613
            · rcases m.htr 1 2 4 (by decide) (by decide) with h614 | h614
              · rcases m.htr 1 2 5 (by decide) (by decide) with h615 | h615
                · linarith only [h0, h6, h615, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h617 | h617
                  · linarith only [h2, h611, h617, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                    · linarith only [h0, h6, h611, h613, h619, hc34, hlam, hphi, u4elo4]
                    · linarith only [h4, h6, h608, h611, h619, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h5, h6, h611, h614, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h4, h6, h611, h613, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h624 | h624
        · linarith only [h4, h6, h608, h624, hc23, hlam, hphi, ht34, u4elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h626 | h626
          · linarith only [h5, h6, h626, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
            · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
              · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                · linarith only [h0, h6, h630, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h632 | h632
                  · linarith only [h608, h626, h632, hc03, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                    · linarith only [h0, h6, h626, h628, h634, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                      · linarith only [h0, h6, h624, h629, h634, h636, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                        · linarith only [h0, h6, h626, h629, h638, hlam]
                        · linarith only [h0, h6, h629, h634, h638, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h628, h629, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h6, h628, hc12, hc25, hlam, hphi]
  · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]

end R2N4
