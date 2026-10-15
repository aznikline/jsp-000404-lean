import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                            · linarith only [h0, h15, h18, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h0, h15, h17, h18, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                            · linarith only [h17, h21, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases h0bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h1, h14, h15, h17, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h1, h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h15, h17, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
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
                                linarith only [h1, h14, h15, h17, h6, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h1, h14, h15, h17, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23_1, u2elo0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p23_1, u2elo0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h3, hlam, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h1, h14, h15, h17, h3, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h14, h15, h17, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23_1, u2elo0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h1, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h4, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h6, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h14, h15, h17, h2, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h2, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h5, hlam, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h7, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h8, hlam, p23_1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                        · linarith only [h0, h13, h15, h16, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                        · linarith only [h15, h3, h50, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                            · rcases h0bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h0, h12, h50, h53, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, h12, h50, h53, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, h12, h50, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h13, h2, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h0, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, h12, h50, h53, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p54_1, u2elo0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, h12, h50, h53, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p54_1, u2elo0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h13, h2, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p54_1, u2elo0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h0, h12, h50, h53, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h3, hlam, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, h12, h3, h50, h53, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p54_1, u2elo0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h13, h2, h3, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p54_1, u2elo0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h4, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h6, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h13, h2, h50, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h2, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h5, hlam, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h7, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h8, hlam, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                            · linarith only [h15, h52, h53, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h12, h15, h52, h81, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h15, h3, h6, h8, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                          · linarith only [h10, h14, h86, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                            · linarith only [h10, h14, h84, h88, hlam]
                            · rcases h0bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h14, h3, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h6, h8, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h8, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h8, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h0, hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h6, h8, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p90_1, u2elo0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h8, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p90_1, u2elo0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h8, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p90_1, u2elo0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h3, hlam, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h3, h8, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p90_1, u2elo0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h3, h8, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p90_1, u2elo0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h1, hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h4, hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h6, hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h10, h14, h8, h84, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h2, hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h5, hlam, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h7, hlam, p90_0]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [h8, hlam, p90_1]
                              · have p90_0 := h90c.1
                                have p90_1 := h90c.2.1
                                have p90_2 := h90c.2.2.1
                                have p90_3 := h90c.2.2.2
                                linarith only [hlam, p90_0]
                        · linarith only [h13, h84, h85, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h12, h14, h3, h6, h8, h84, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h12, h13, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h119, h12, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                      · linarith only [h12, h122, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                        · linarith only [h12, h124, h3, h6, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
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
                                linarith only [h119, h127, h3, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h127, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h126, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h127, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p128_1, u2elo0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h3, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h127, h3, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h3, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h1, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h4, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h6, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, h7, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h2, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h5, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h7, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h8, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                            · linarith only [h10, h126, h127, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h12, h121, h126, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                      · linarith only [h12, h156, h9, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h119, h12, h121, h158, h3, h6, h8, h9, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                          · linarith only [h10, h121, h160, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                            · linarith only [h12, h121, h162, h3, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h12, h162, h3, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h10, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
          · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h1, h173, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
                          · linarith only [h1, h169, h177, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                            · linarith only [h168, h175, h179, h8, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h0bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h0, h168, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h176, h179, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p181_1]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                rcases p181_3 (m.d 0 1) (by simp) with h185 | h185
                                · rcases p181_3 (m.d 0 2) (by simp) with h186 | h186
                                  · linarith only [h0, h186, hlam]
                                  · linarith only [h186, h4, hlam]
                                · linarith only [h1, h185, hlam]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                rcases p181_3 (m.d 0 1) (by simp) with h190 | h190
                                · rcases p181_3 (m.d 0 2) (by simp) with h191 | h191
                                  · linarith only [h0, h191, hlam]
                                  · linarith only [h191, h5, hlam]
                                · linarith only [h190, h2, hlam]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h0, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h176, h179, h3, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p181_1]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h1, h169, h175, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p181_1, u2elo0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h1, h169, h175, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p181_1, u2elo0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h0, h168, h176, h179, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p181_1]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h3, hlam, p181_1]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h1, h169, h175, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p181_1, u2elo0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h1, h169, h175, h3, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p181_1, u2elo0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h1, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h4, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h6, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h8, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h2, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h5, hlam, p181_1]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h7, hlam, p181_0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [h1, h169, h175, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p181_1, u2elo0]
                              · have p181_0 := h181c.1
                                have p181_1 := h181c.2.1
                                have p181_2 := h181c.2.2.1
                                have p181_3 := h181c.2.2.2
                                linarith only [hlam, p181_0]
                        · linarith only [h0, h168, h172, h175, h176, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
                        · linarith only [h175, h216, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                          · linarith only [h1, h171, h175, h218, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                            · linarith only [h1, h171, h220, h8, hlam]
                            · rcases h0bigk with h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h0, h168, h172, h175, h220, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h175, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, h171, h175, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h175, h220, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h0, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h175, h220, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, h171, h175, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p222_1, u2elo0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p222_1, u2elo0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h0, h168, h172, h175, h220, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h3, hlam, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, h171, h175, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p222_1, u2elo0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, h171, h175, h3, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p222_1, u2elo0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h4, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h6, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h8, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h2, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h5, hlam, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h7, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, h171, h175, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                  · linarith only [h171, h172, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
                  · linarith only [h171, h249, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
                    · linarith only [h1, h251, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h168, h171, h253, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h168, h249, h255, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                          · linarith only [h168, h169, h249, h257, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                            · linarith only [h259, h6, h8, hlam]
                            · rcases h0bigk with h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h259, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h0, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h259, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p261_1, u2elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p261_1, u2elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h3, hlam, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p261_1, u2elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h3, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p261_1, u2elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h1, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h4, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h6, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h8, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h2, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h5, hlam, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h7, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h168, h171, h6, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
              · linarith only [h168, h170, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h168, h169, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h168, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
        · linarith only [h290, h6, h7, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
          · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
            · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
              · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                  · linarith only [h0, h292, h296, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                    · linarith only [h1, h290, h298, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                        · linarith only [h3, h301, h7, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                          · linarith only [h1, h290, h293, h303, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h1, h290, h300, h305, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases h0bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, h294, h301, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h3, h300, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 1) (by simp) with h311 | h311
                                · rcases p307_3 (m.d 0 2) (by simp) with h312 | h312
                                  · linarith only [h0, h312, hlam]
                                  · linarith only [h312, h4, hlam]
                                · linarith only [h1, h311, hlam]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, h292, h296, h300, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h3, h300, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p307_1, u2elo0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, h293, h300, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p307_1, u2elo0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, h292, h296, h300, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p307_1, u2elo0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h7, hc01, hc35, hlam, hphi, ht12, ht23, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h3, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, h293, h300, h305, h7, hc34, hc45, hlam, hphi, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h7, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h4, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h6, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h290, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h5, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, h3, h300, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, h293, h300, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p307_1, u2elo0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                      · linarith only [h300, h6, h7, hc23, hc35, hlam, hphi]
                · linarith only [h295, h6, h7, hc13, hc35, hlam, hphi]
              · linarith only [h292, h294, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h292, h293, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h292, h3, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h342 | h342
      · rcases m.htr 0 4 5 (by decide) (by decide) with h343 | h343
        · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
          · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
            · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
              · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                · linarith only [h342, h344, h347, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h351 | h351
                      · linarith only [h3, h351, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h355 | h355
                            · rcases h0bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h3, h353, h355, hc01, hc45, hlam, hphi, ht0b, ht5b, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h3, h353, h355, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                rcases p356_3 (m.d 0 1) (by simp) with h361 | h361
                                · rcases p356_3 (m.d 0 2) (by simp) with h362 | h362
                                  · linarith only [h0, h362, hlam]
                                  · linarith only [h362, h5, hlam]
                                · linarith only [h2, h361, hlam]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h0, hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h3, h353, h355, hc02, hc45, hlam, hphi, ht0b, ht5b, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h1, h344, h347, h353, h355, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p356_1, u2elo0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h2, h346, h353, h355, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p356_1, u2elo0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h6, hc01, hc34, hlam, hphi, ht12, ht23, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h3, hlam, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h6, hlam, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h4, h6, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p356_1, u2elo0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h1, hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h4, hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p356_1, u2elo0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h2, h346, h353, h355, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p356_1, u2elo0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h2, hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h5, hlam, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h342, hlam, p356_0]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [h343, hlam, p356_1]
                              · have p356_0 := h356c.1
                                have p356_1 := h356c.2.1
                                have p356_2 := h356c.2.2.1
                                have p356_3 := h356c.2.2.2
                                linarith only [hlam, p356_0]
                            · linarith only [h343, h355, h6, hlam]
                          · linarith only [h343, h351, h353, h354, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h342, h353, h6, hc23, hc34, hlam, hphi]
                    · linarith only [h343, h347, h349, h350, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · linarith only [h342, h349, h6, hc13, hc34, hlam, hphi]
              · linarith only [h346, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h344, h345, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h3, h344, hc12, hlam, hphi, u2elo0]
        · linarith only [h342, h343, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h395 | h395
        · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
          · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
            · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
              · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                · linarith only [h1, h399, h6, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
                  · linarith only [h3, h342, h399, h401, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                      · linarith only [h3, h399, h404, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                        · linarith only [h3, h342, h406, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                            · rcases h0bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h0, h397, h406, h408, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                rcases p410_3 (m.d 0 1) (by simp) with h413 | h413
                                · rcases p410_3 (m.d 0 2) (by simp) with h414 | h414
                                  · linarith only [h0, h414, hlam]
                                  · linarith only [h3, h414, hlam]
                                · linarith only [h413, hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h1, h397, h408, hc01, hc45, hlam, hphi, ht0b, ht5b, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                rcases p410_3 (m.d 0 1) (by simp) with h419 | h419
                                · rcases p410_3 (m.d 0 2) (by simp) with h420 | h420
                                  · linarith only [h0, h420, hlam]
                                  · linarith only [h420, h5, hlam]
                                · linarith only [h2, h419, hlam]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h0, hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p410_1, u2elo0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h1, h397, h408, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h2, h396, h401, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p410_1, u2elo0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h342, h409, hc01, hc34, hlam, hphi, ht12, ht23, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h3, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h6, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h342, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h1, hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h4, hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p410_1, u2elo0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h2, h396, h4, h401, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p410_1, u2elo0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h2, hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h5, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p410_1, u2elo0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h395, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                            · linarith only [h0, h397, h408, h409, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h445 | h445
                            · rcases h0bigk with h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h1, h4, h403, h408, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                rcases p446_3 (m.d 0 1) (by simp) with h449 | h449
                                · rcases p446_3 (m.d 0 2) (by simp) with h450 | h450
                                  · linarith only [h0, h450, hlam]
                                  · linarith only [h3, h450, hlam]
                                · linarith only [h449, hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h1, h403, h404, h408, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h395, h404, h408, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h0, hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p446_1, u2elo0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h1, h403, h404, h408, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p446_1, u2elo0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p446_1, u2elo0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h3, hlam, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h6, hlam, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h342, hlam, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h1, hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h4, hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p446_1, u2elo0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h2, h4, h403, h404, h408, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p446_1, u2elo0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h2, hlam, p446_0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h5, hlam, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p446_1, u2elo0]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [h395, hlam, p446_1]
                              · have p446_0 := h446c.1
                                have p446_1 := h446c.2.1
                                have p446_2 := h446c.2.2.1
                                have p446_3 := h446c.2.2.2
                                linarith only [hlam, p446_0]
                            · linarith only [h0, h3, h397, h403, h445, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                      · linarith only [h395, h403, h477, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h479 | h479
                        · linarith only [h395, h396, h399, h4, h403, h479, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h481 | h481
                          · linarith only [h396, h399, h4, h403, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                            · rcases h0bigk with h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                rcases p484_3 (m.d 0 1) (by simp) with h487 | h487
                                · rcases p484_3 (m.d 0 2) (by simp) with h488 | h488
                                  · linarith only [h0, h488, hlam]
                                  · linarith only [h3, h488, hlam]
                                · linarith only [h487, hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h395, h396, h399, h403, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h395, h396, h399, h403, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h0, hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p484_1, u2elo0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h395, h396, h399, h403, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p484_1, u2elo0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h3, hlam, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h6, hlam, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h342, hlam, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h1, hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h4, hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p484_1, u2elo0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h2, hlam, p484_0]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h5, hlam, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h3, h342, hc23, hc35, hlam, hphi, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [h395, hlam, p484_1]
                              · have p484_0 := h484c.1
                                have p484_1 := h484c.2.1
                                have p484_2 := h484c.2.2.1
                                have p484_3 := h484c.2.2.2
                                linarith only [hlam, p484_0]
                            · linarith only [h395, h483, h6, hlam]
              · linarith only [h398, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h396, h397, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h3, h396, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
          · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
            · rcases m.htr 1 2 5 (by decide) (by decide) with h520 | h520
              · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
                · linarith only [h1, h521, h6, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
                  · linarith only [h3, h342, h521, h523, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h525 | h525
                    · linarith only [h1, h395, h525, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h527 | h527
                      · linarith only [h3, h521, h527, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h529 | h529
                        · linarith only [h0, h342, h519, h527, h529, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h531 | h531
                          · linarith only [h0, h395, h519, h531, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h533 | h533
                            · rcases h0bigk with h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h0, h520, h527, h531, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                rcases p534_3 (m.d 0 1) (by simp) with h537 | h537
                                · rcases p534_3 (m.d 0 2) (by simp) with h538 | h538
                                  · linarith only [h0, h538, hlam]
                                  · linarith only [h3, h538, hlam]
                                · linarith only [h537, hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                rcases p534_3 (m.d 0 1) (by simp) with h542 | h542
                                · rcases p534_3 (m.d 0 2) (by simp) with h543 | h543
                                  · linarith only [h0, h543, hlam]
                                  · linarith only [h4, h543, hlam]
                                · linarith only [h1, h542, hlam]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                rcases p534_3 (m.d 0 1) (by simp) with h547 | h547
                                · rcases p534_3 (m.d 0 2) (by simp) with h548 | h548
                                  · linarith only [h0, h548, hlam]
                                  · linarith only [h5, h548, hlam]
                                · linarith only [h2, h547, hlam]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h0, hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p534_1, u2elo0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h1, h519, h527, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p534_1, u2elo0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h1, h395, h519, h527, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p534_1, u2elo0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h0, h520, h527, h531, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h3, hlam, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h6, hlam, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h342, hlam, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h1, hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h4, hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h395, h533, hc03, hc34, hlam, hphi, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h395, hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h2, hlam, p534_0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h5, hlam, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p534_1, u2elo0]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [h395, h533, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p534_1]
                              · have p534_0 := h534c.1
                                have p534_1 := h534c.2.1
                                have p534_2 := h534c.2.2.1
                                have p534_3 := h534c.2.2.2
                                linarith only [hlam, p534_0]
                            · rcases h0bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, h520, h527, h531, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h575 | h575
                                · rcases p572_3 (m.d 0 2) (by simp) with h576 | h576
                                  · linarith only [h0, h576, hlam]
                                  · linarith only [h3, h576, hlam]
                                · linarith only [h575, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h580 | h580
                                · rcases p572_3 (m.d 0 2) (by simp) with h581 | h581
                                  · linarith only [h0, h581, hlam]
                                  · linarith only [h4, h581, hlam]
                                · linarith only [h1, h580, hlam]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h585 | h585
                                · rcases p572_3 (m.d 0 2) (by simp) with h586 | h586
                                  · linarith only [h0, h586, hlam]
                                  · linarith only [h5, h586, hlam]
                                · linarith only [h2, h585, hlam]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u2elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h1, h519, h527, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u2elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p572_1, u2elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, h520, h527, h531, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h6, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h342, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h1, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h4, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u2elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h395, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h2, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h5, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u2elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h1, h342, h519, h527, hc23, hc35, hlam, hphi, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
              · linarith only [h5, h520, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h518, h519, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h3, h518, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h613 | h613
    · rcases m.htr 0 3 5 (by decide) (by decide) with h614 | h614
      · linarith only [h3, h5, h614, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h616 | h616
        · linarith only [h4, h5, h616, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
          · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
            · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
              · linarith only [h0, h5, h620, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
                · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
                  · linarith only [h0, h5, h614, h618, h623, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h625 | h625
                    · linarith only [h1, h4, h5, h616, h625, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                      · linarith only [h0, h5, h618, h627, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h3, h5, h613, h627, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h3, h5, h613, h622, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h4, h5, h619, hc12, hlam, hphi, u2elo4]
          · linarith only [h3, h5, h618, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h633 | h633
      · linarith only [h4, h5, h613, h633, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h635 | h635
        · linarith only [h4, h5, h635, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
          · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
            · rcases m.htr 1 2 5 (by decide) (by decide) with h639 | h639
              · linarith only [h5, h639, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                · linarith only [h0, h5, h613, h637, h641, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                  · linarith only [h0, h5, h633, h638, h641, h643, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h645 | h645
                    · linarith only [h0, h5, h635, h638, h645, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h647 | h647
                      · linarith only [h3, h5, h641, h647, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h649 | h649
                        · linarith only [h0, h5, h633, h638, h647, h649, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h651 | h651
                          · linarith only [h0, h5, h635, h638, h651, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h653 | h653
                            · linarith only [h3, h5, h651, h653, hc23, hc34, hlam, hphi]
                            · rcases h0bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, h638, h647, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                rcases p655_3 (m.d 0 1) (by simp) with h658 | h658
                                · rcases p655_3 (m.d 0 2) (by simp) with h659 | h659
                                  · linarith only [h0, h659, hlam]
                                  · linarith only [h3, h659, hlam]
                                · linarith only [h658, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                rcases p655_3 (m.d 0 1) (by simp) with h663 | h663
                                · rcases p655_3 (m.d 0 2) (by simp) with h664 | h664
                                  · linarith only [h0, h664, hlam]
                                  · linarith only [h4, h664, hlam]
                                · linarith only [h1, h663, hlam]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, h5, h638, h647, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p655_1, u2elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h1, h5, h637, h641, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p655_1, u2elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h5, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, h638, h647, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h3, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h613, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h633, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h1, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h4, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h3, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p655_1, u2elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h635, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h2, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, h638, h647, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p655_1, u2elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p655_1, u2elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
            · linarith only [h4, h638, hc12, hlam, hphi, u2elo0]
          · linarith only [h3, h5, h637, hc12, hlam, hphi, u2elo4]

end R2N4
