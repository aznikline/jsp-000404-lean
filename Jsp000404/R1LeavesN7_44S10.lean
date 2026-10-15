import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
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
                              · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h17, h21, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases h2bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
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
                                  linarith only [h0, h16, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  rcases p23_3 (m.d 0 2) (by simp) with h27 | h27
                                  · rcases p23_3 (m.d 1 2) (by simp) with h28 | h28
                                    · linarith only [h0, h28, hlam]
                                    · linarith only [h10, h28, hlam]
                                  · linarith only [h27, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  rcases p23_3 (m.d 0 2) (by simp) with h32 | h32
                                  · rcases p23_3 (m.d 1 2) (by simp) with h33 | h33
                                    · linarith only [h0, h33, hlam]
                                    · linarith only [h11, h33, hlam]
                                  · linarith only [h32, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h16, h21, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h3, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h9, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p23_1, u3elo2]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h4, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h10, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h15, hlam, p23_0]
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
                                  linarith only [h5, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h11, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h16, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h15, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                          · linarith only [h16, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                            · linarith only [h10, h14, h61, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                              · linarith only [h10, h14, h59, h63, hlam]
                              · rcases h2bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, h60, hc01, hc35, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  rcases p65_3 (m.d 0 2) (by simp) with h69 | h69
                                  · rcases p65_3 (m.d 1 2) (by simp) with h70 | h70
                                    · linarith only [h0, h70, hlam]
                                    · linarith only [h10, h70, hlam]
                                  · linarith only [h69, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  rcases p65_3 (m.d 0 2) (by simp) with h74 | h74
                                  · rcases p65_3 (m.d 1 2) (by simp) with h75 | h75
                                    · linarith only [h0, h75, hlam]
                                    · linarith only [h11, h75, hlam]
                                  · linarith only [h74, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, hlam, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h60, h63, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, h59, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h3, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h9, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h59, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p65_1, u3elo1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h4, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h10, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h59, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h61, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h5, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h11, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h60, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, h5, h59, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                          · linarith only [h60, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h59, h6, hc23, hlam, hphi, u3elo0]
                    · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                  · linarith only [h12, h6, h9, hc23, hlam, hphi, u3elo0]
                · linarith only [h11, h5, h6, h8, h9, hc23, hlam, hphi, u3elo0]
              · linarith only [h10, h4, h6, h9, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
              · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                            · linarith only [h105, h112, h3, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                            · linarith only [h105, h109, h110, h112, h3, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h111, h9, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h110, h9, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h105, h109, h119, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                              · linarith only [h105, h109, h117, h121, hlam]
                              · rcases h2bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, h106, hc01, hc25, hlam, hphi, ht0b, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, h106, h118, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h127 | h127
                                  · rcases p123_3 (m.d 1 2) (by simp) with h128 | h128
                                    · linarith only [h0, h128, hlam]
                                    · linarith only [h105, h128, hlam]
                                  · linarith only [h127, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h132 | h132
                                  · rcases p123_3 (m.d 1 2) (by simp) with h133 | h133
                                    · linarith only [h0, h133, hlam]
                                    · linarith only [h106, h133, hlam]
                                  · linarith only [h132, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h9, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h9, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h119, h3, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p123_1, u3elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h3, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p123_1, u3elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p123_1, u3elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h119, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p123_1, u3elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h4, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h105, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h119, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h5, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h106, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h118, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h106, h117, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                          · linarith only [h118, h9, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h105, h117, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h108, h7, hc13, hlam, hphi, u3elo0]
                  · linarith only [h105, h107, h6, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h105, h106, h163, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                            · linarith only [h105, h106, h163, h166, h167, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h106, h167, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h162, h163, h166, h6, h8, h9, hc13, hlam, hphi, u3elo0]
                        · linarith only [h165, h9, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h105, h162, h7, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h105, h161, h6, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                              · rcases h2bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, h174, h179, h181, hc01, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, h105, h174, h178, h179, h181, hc01, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, h105, h174, h179, h181, hc01, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  rcases p182_3 (m.d 0 2) (by simp) with h187 | h187
                                  · rcases p182_3 (m.d 1 2) (by simp) with h188 | h188
                                    · linarith only [h0, h188, hlam]
                                    · linarith only [h174, h188, hlam]
                                  · linarith only [h187, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, hlam, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h9, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h105, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h105, h178, h179, h181, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h3, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p182_1, u3elo0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p182_1, u3elo0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h179, h181, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p182_1, u3elo0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h4, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h174, h179, h181, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h178, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h179, h181, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p182_1, u3elo0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h5, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h174, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h179, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h180, hlam, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                              · linarith only [h174, h180, h181, h3, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h105, h174, h177, h180, h2, hc01, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h179, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h178, h6, h9, hc13, hlam, hphi, u3elo0]
                      · linarith only [h105, h174, h177, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                    · linarith only [h105, h174, h175, h176, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · linarith only [h175, h6, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                              · rcases h2bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  rcases p226_3 (m.d 0 2) (by simp) with h228 | h228
                                  · rcases p226_3 (m.d 1 2) (by simp) with h229 | h229
                                    · linarith only [h0, h229, hlam]
                                    · rcases p226_3 (m.d 2 3) (by simp) with h231 | h231
                                      · linarith only [h231, h3, hlam]
                                      · linarith only [h231, h9, hlam]
                                  · linarith only [h0, h228, hlam]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h0, h219, h225, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p226_1]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h0, h105, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p226_1]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h0, h174, h219, h225, h3, h9, hc01, hc12, hc45, hlam, hphi, ht0b, ht23, ht5b, p226_1, u3elo0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h0, hlam, p226_1]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h9, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h105, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h174, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h3, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p226_1, u3elo0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h105, h3, hc12, hlam, hphi, ht23, p226_1, u3elo0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h174, h3, hc12, hlam, hphi, ht23, p226_1, u3elo0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h4, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p226_1]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h222, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h174, h4, h6, hc12, hlam, hphi, ht23, p226_1, u3elo0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h5, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p226_1]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h223, hlam, p226_0]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [h224, hlam, p226_1]
                                · have p226_0 := h226c.1
                                  have p226_1 := h226c.2.1
                                  have p226_2 := h226c.2.2.1
                                  have p226_3 := h226c.2.2.2
                                  linarith only [hlam, p226_0]
                              · rcases h2bigk with h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  rcases p258_3 (m.d 0 2) (by simp) with h260 | h260
                                  · rcases p258_3 (m.d 1 2) (by simp) with h261 | h261
                                    · linarith only [h0, h261, hlam]
                                    · rcases p258_3 (m.d 2 3) (by simp) with h263 | h263
                                      · linarith only [h263, h3, hlam]
                                      · linarith only [h263, h9, hlam]
                                  · linarith only [h0, h260, hlam]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h0, h105, h221, h225, h4, h6, h9, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p258_1, u3elo0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h0, h105, h221, h225, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p258_1]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h0, h105, h174, h221, h225, h4, h6, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p258_1, u3elo0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h0, hlam, p258_1]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h9, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h105, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h174, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h3, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p258_1]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h105, h221, h225, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p258_1, u3elo0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h174, h3, hc12, hlam, hphi, ht23, p258_1, u3elo0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h4, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p258_1]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h222, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h174, h4, h6, hc12, hlam, hphi, ht23, p258_1, u3elo0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h5, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p258_1]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h223, hlam, p258_0]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [h224, hlam, p258_1]
                                · have p258_0 := h258c.1
                                  have p258_1 := h258c.2.1
                                  have p258_2 := h258c.2.2.1
                                  have p258_3 := h258c.2.2.2
                                  linarith only [hlam, p258_0]
                            · linarith only [h105, h2, h221, h224, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h220, h223, h9, hlam]
                        · linarith only [h222, h6, h9, hc13, hlam, hphi, u3elo0]
                      · linarith only [h105, h221, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                    · linarith only [h219, h220, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h219, h6, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
            · rcases m.htr 1 2 4 (by decide) (by decide) with h297 | h297
              · rcases m.htr 1 2 5 (by decide) (by decide) with h298 | h298
                · rcases m.htr 1 3 4 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                      · linarith only [h2, h301, h8, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h305, h4, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                              · linarith only [h303, h307, h4, h8, hlam]
                              · rcases h2bigk with h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, h296, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, h304, hc01, hc35, hlam, hphi, ht0b, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  rcases p309_3 (m.d 0 2) (by simp) with h313 | h313
                                  · rcases p309_3 (m.d 1 2) (by simp) with h314 | h314
                                    · linarith only [h0, h314, hlam]
                                    · linarith only [h297, h314, hlam]
                                  · linarith only [h313, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  rcases p309_3 (m.d 0 2) (by simp) with h318 | h318
                                  · rcases p309_3 (m.d 1 2) (by simp) with h319 | h319
                                    · linarith only [h0, h319, hlam]
                                    · linarith only [h298, h319, hlam]
                                  · linarith only [h318, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, hlam, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h304, h307, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, h303, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h3, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h296, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h303, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p309_1, u3elo2]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, h296, hc01, hc25, hlam, hphi, ht0b, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h4, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h297, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h303, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h305, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h5, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h298, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h304, hlam, p309_0]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [h0, h303, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p309_1]
                                · have p309_0 := h309c.1
                                  have p309_1 := h309c.2.1
                                  have p309_2 := h309c.2.2.1
                                  have p309_3 := h309c.2.2.2
                                  linarith only [hlam, p309_0]
                          · linarith only [h304, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h303, h6, hc23, hlam, hphi, u3elo0]
                    · linarith only [h300, h7, hc13, hlam, hphi, u3elo0]
                  · linarith only [h296, h299, h6, hc23, hlam, hphi, u3elo0]
                · linarith only [h296, h298, h5, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h296, h297, h4, h7, h8, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
              · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h353 | h353
                      · linarith only [h296, h3, h349, h353, h4, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h356 | h356
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
                            · linarith only [h357, h4, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                              · linarith only [h355, h359, h4, h8, hlam]
                              · rcases h2bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h0, h350, hc01, hc25, hlam, hphi, ht0b, ht5b, p361_1]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h0, h296, h350, h356, hc01, hc35, hlam, hphi, ht0b, ht5b, p361_1]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  rcases p361_3 (m.d 0 2) (by simp) with h365 | h365
                                  · rcases p361_3 (m.d 1 2) (by simp) with h366 | h366
                                    · linarith only [h0, h366, hlam]
                                    · linarith only [h349, h366, hlam]
                                  · linarith only [h365, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  rcases p361_3 (m.d 0 2) (by simp) with h370 | h370
                                  · rcases p361_3 (m.d 1 2) (by simp) with h371 | h371
                                    · linarith only [h0, h371, hlam]
                                    · linarith only [h350, h371, hlam]
                                  · linarith only [h370, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h0, hlam, p361_1]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h296, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h296, h355, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p361_1]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h296, h3, h355, h357, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p361_1, u3elo0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h3, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p361_1, u3elo0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h3, h355, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p361_1, u3elo0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h3, h355, h357, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p361_1, u3elo0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h4, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h349, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h355, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h357, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h5, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h350, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h356, hlam, p361_0]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [h350, h355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p361_1]
                                · have p361_0 := h361c.1
                                  have p361_1 := h361c.2.1
                                  have p361_2 := h361c.2.2.1
                                  have p361_3 := h361c.2.2.2
                                  linarith only [hlam, p361_0]
                          · linarith only [h296, h356, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h296, h349, h355, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h352, h7, hc13, hlam, hphi, u3elo0]
                  · linarith only [h296, h349, h351, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                      · linarith only [h296, h349, h401, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                            · linarith only [h349, h350, h405, h5, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                              · linarith only [h349, h350, h403, h407, h5, h8, hlam]
                              · rcases h2bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h349, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h296, h349, h403, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 2) (by simp) with h413 | h413
                                  · rcases p409_3 (m.d 1 2) (by simp) with h414 | h414
                                    · linarith only [h0, h414, hlam]
                                    · linarith only [h349, h414, hlam]
                                  · linarith only [h413, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h349, h350, h403, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h296, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h350, h403, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h350, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h3, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h3, h403, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p409_1, u3elo0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h4, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h349, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h403, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h405, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h5, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h349, h403, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h404, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h403, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                          · linarith only [h404, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h296, h403, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h400, h7, hc13, hlam, hphi, u3elo0]
                  · linarith only [h296, h349, h399, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
                · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                      · linarith only [h349, h4, h443, h446, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h349, h443, h446, hlam]
                    · linarith only [h349, h4, h443, h444, h445, h7, h8, hc25, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · linarith only [h444, h6, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                      · linarith only [h349, h4, h453, h8, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                            · linarith only [h4, h457, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h459 | h459
                              · linarith only [h349, h4, h451, h459, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h2bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  rcases p461_3 (m.d 0 2) (by simp) with h463 | h463
                                  · rcases p461_3 (m.d 1 2) (by simp) with h464 | h464
                                    · linarith only [h0, h464, hlam]
                                    · rcases p461_3 (m.d 2 3) (by simp) with h466 | h466
                                      · linarith only [h3, h466, hlam]
                                      · linarith only [h296, h466, hlam]
                                  · linarith only [h0, h463, hlam]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h0, h296, h452, hc01, hc35, hlam, hphi, ht0b, ht5b, p461_1]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h0, h349, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p461_1]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h0, h349, h457, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p461_1]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h0, hlam, p461_1]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h296, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h349, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h443, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h3, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p461_1]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h3, h349, hc12, hlam, hphi, ht23, p461_1, u3elo0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h3, h349, h457, hc12, hlam, hphi, ht23, p461_1, u3elo0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h4, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p461_1]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h455, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h457, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h5, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h5, h7, hc12, hlam, hphi, ht23, p461_1, u3elo0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h456, hlam, p461_0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [h5, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p461_1, u3elo0]
                                · have p461_0 := h461c.1
                                  have p461_1 := h461c.2.1
                                  have p461_2 := h461c.2.2.1
                                  have p461_3 := h461c.2.2.2
                                  linarith only [hlam, p461_0]
                          · linarith only [h456, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h296, h455, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h452, h7, hc13, hlam, hphi, u3elo0]
                  · linarith only [h296, h451, h6, hc12, hlam, hphi, ht23, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h497 | h497
          · linarith only [h497, h6, h7, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
            · rcases m.htr 1 2 4 (by decide) (by decide) with h500 | h500
              · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                    · linarith only [h1, h503, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h505 | h505
                      · linarith only [h1, h497, h502, h505, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                          · linarith only [h1, h499, h508, h7, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h510 | h510
                            · linarith only [h4, h505, h510, h6, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h512 | h512
                              · linarith only [h497, h512, h6, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · rcases h2bigk with h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h501, h508, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h507, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  rcases p514_3 (m.d 0 2) (by simp) with h518 | h518
                                  · rcases p514_3 (m.d 1 2) (by simp) with h519 | h519
                                    · linarith only [h0, h519, hlam]
                                    · linarith only [h500, h519, hlam]
                                  · linarith only [h518, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h507, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, hlam, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h507, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h507, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h507, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h3, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h499, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h1, h499, h507, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p514_1, u3elo4]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h508, hlam, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h4, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h500, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h507, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h510, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h5, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h501, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h2, h501, h507, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                        · linarith only [h507, h6, h7, hc23, hlam, hphi, u3elo4]
                  · linarith only [h502, h6, h7, hc13, hlam, hphi, u3elo4]
                · linarith only [h499, h5, h501, h7, hc23, hlam, hphi, u3elo4]
              · linarith only [h4, h499, h500, h6, h7, hc23, hlam, hphi, u3elo4]
            · linarith only [h3, h499, h7, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h549 | h549
        · rcases m.htr 0 4 5 (by decide) (by decide) with h550 | h550
          · rcases m.htr 1 2 3 (by decide) (by decide) with h551 | h551
            · rcases m.htr 1 2 4 (by decide) (by decide) with h552 | h552
              · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                  · linarith only [h1, h554, h6, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                        · linarith only [h1, h551, h558, h6, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h562 | h562
                              · rcases h2bigk with h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, h552, h558, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, h560, h562, hc01, hc45, hlam, hphi, ht0b, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, h558, h560, h562, hc01, hc45, hlam, hphi, ht0b, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  rcases p563_3 (m.d 0 2) (by simp) with h568 | h568
                                  · rcases p563_3 (m.d 1 2) (by simp) with h569 | h569
                                    · linarith only [h0, h569, hlam]
                                    · linarith only [h553, h569, hlam]
                                  · linarith only [h568, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, hlam, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h560, h562, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, h558, h560, h562, hc01, hc45, hlam, hphi, ht0b, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h3, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h551, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h558, hlam, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h1, h551, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo3]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h4, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h552, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h560, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h0, h552, h560, h562, hc01, hc45, hlam, hphi, ht0b, ht5b, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h5, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h553, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h560, hlam, p563_0]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [h561, hlam, p563_1]
                                · have p563_0 := h563c.1
                                  have p563_1 := h563c.2.1
                                  have p563_2 := h563c.2.2.1
                                  have p563_3 := h563c.2.2.2
                                  linarith only [hlam, p563_0]
                              · linarith only [h550, h562, h6, hlam]
                            · linarith only [h2, h549, h557, h558, h560, h561, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h549, h560, h6, hc23, hlam, hphi, u3elo3]
                      · linarith only [h549, h550, h554, h557, h6, hc13, hlam, hphi, u3elo3]
                    · linarith only [h549, h551, h556, h6, hc23, hlam, hphi, u3elo3]
                · linarith only [h5, h549, h553, h6, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h4, h551, h552, h6, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h551, h6, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h549, h550, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
          · rcases m.htr 1 2 3 (by decide) (by decide) with h603 | h603
            · rcases m.htr 1 2 4 (by decide) (by decide) with h604 | h604
              · rcases m.htr 1 2 5 (by decide) (by decide) with h605 | h605
                · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                  · linarith only [h1, h6, h606, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
                    · linarith only [h1, h549, h608, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                        · linarith only [h1, h6, h603, h611, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                          · linarith only [h1, h549, h603, h613, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h616 | h616
                              · rcases h2bigk with h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h604, h613, h615, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  rcases p617_3 (m.d 0 2) (by simp) with h620 | h620
                                  · rcases p617_3 (m.d 1 2) (by simp) with h621 | h621
                                    · linarith only [h0, h621, hlam]
                                    · linarith only [h603, h621, hlam]
                                  · linarith only [h620, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h615, hc01, hc45, hlam, hphi, ht0b, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  rcases p617_3 (m.d 0 2) (by simp) with h626 | h626
                                  · rcases p617_3 (m.d 1 2) (by simp) with h627 | h627
                                    · linarith only [h0, h627, hlam]
                                    · linarith only [h605, h627, hlam]
                                  · linarith only [h626, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h615, hc01, hc45, hlam, hphi, ht0b, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h3, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h603, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h611, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h613, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h4, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h604, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h604, h613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h5, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h605, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h615, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                              · linarith only [h6, h602, h616, hlam]
                            · linarith only [h6, h602, h611, h615, hc23, hlam, hphi, u3elo3]
                      · linarith only [h6, h602, h603, h606, h610, hc23, hlam, hphi, u3elo3]
                · linarith only [h5, h549, h603, h605, hc23, hlam, hphi, u3elo4]
              · linarith only [h4, h6, h603, h604, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h6, h603, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
            · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
              · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
                · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
                  · linarith only [h6, h660, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                    · linarith only [h1, h549, h662, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h664 | h664
                      · linarith only [h6, h602, h660, h664, hc03, hlam, hphi, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h666 | h666
                        · linarith only [h1, h6, h657, h666, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h668 | h668
                          · linarith only [h1, h549, h657, h668, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h670 | h670
                            · linarith only [h0, h6, h602, h658, h670, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h672 | h672
                              · linarith only [h1, h6, h602, h657, h672, hc23, hlam, hphi, u3elo3]
                              · rcases h2bigk with h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h0, h657, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  rcases p674_3 (m.d 0 2) (by simp) with h677 | h677
                                  · rcases p674_3 (m.d 1 2) (by simp) with h678 | h678
                                    · linarith only [h0, h678, hlam]
                                    · linarith only [h657, h678, hlam]
                                  · linarith only [h677, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  rcases p674_3 (m.d 0 2) (by simp) with h682 | h682
                                  · rcases p674_3 (m.d 1 2) (by simp) with h683 | h683
                                    · linarith only [h0, h683, hlam]
                                    · linarith only [h658, h683, hlam]
                                  · linarith only [h682, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  rcases p674_3 (m.d 0 2) (by simp) with h687 | h687
                                  · rcases p674_3 (m.d 1 2) (by simp) with h688 | h688
                                    · linarith only [h0, h688, hlam]
                                    · linarith only [h659, h688, hlam]
                                  · linarith only [h687, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h0, hlam, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h0, h666, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h0, h666, h670, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h3, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h657, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h666, hlam, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h668, hlam, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h4, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h658, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h670, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h5, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h659, hlam, p674_0]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h2, h549, h659, hc23, hlam, hphi, p674_1, u3elo4]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [h2, h549, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p674_1, u3elo4]
                                · have p674_0 := h674c.1
                                  have p674_1 := h674c.2.1
                                  have p674_2 := h674c.2.2.1
                                  have p674_3 := h674c.2.2.2
                                  linarith only [hlam, p674_0]
                · linarith only [h5, h549, h657, h659, hc23, hlam, hphi, u3elo4]
              · linarith only [h4, h6, h657, h658, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h6, h657, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h715 | h715
      · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
        · linarith only [h3, h5, h716, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
          · linarith only [h3, h5, h715, h716, h718, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
            · rcases m.htr 1 2 4 (by decide) (by decide) with h721 | h721
              · rcases m.htr 1 2 5 (by decide) (by decide) with h722 | h722
                · linarith only [h0, h5, h722, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h724 | h724
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h725 | h725
                    · linarith only [h1, h716, h725, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h727 | h727
                      · linarith only [h0, h5, h718, h721, h727, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h730 | h730
                          · linarith only [h3, h5, h716, h730, hlam]
                          · linarith only [h0, h5, h720, h730, hc23, hlam, hphi, u3elo4]
                        · linarith only [h1, h724, h729, hc23, hlam, hphi, u3elo0]
                  · linarith only [h715, h716, h724, hc13, hlam, hphi, u3elo4]
              · linarith only [h4, h5, h720, h721, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3, h5, h716, h720, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h737 | h737
        · linarith only [h3, h5, h715, h737, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
          · linarith only [h4, h5, h739, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
            · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
              · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                · linarith only [h0, h5, h743, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                  · linarith only [h1, h715, h745, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                    · linarith only [h0, h1, h5, h715, h737, h741, h747, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
                      · linarith only [h0, h1, h5, h715, h737, h739, h742, h749, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                        · linarith only [h1, h715, h741, h751, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                          · linarith only [h3, h5, h737, h753, hlam]
                          · linarith only [h0, h5, h742, h751, h753, hc23, hlam, hphi, u3elo4]
              · linarith only [h4, h5, h742, hc12, hc25, hlam, hphi]
            · linarith only [h3, h5, h737, h741, hc12, hlam, hphi, ht23, u3elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h758 | h758
    · rcases m.htr 0 3 4 (by decide) (by decide) with h759 | h759
      · linarith only [h3, h4, h759, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h761 | h761
        · rcases m.htr 0 4 5 (by decide) (by decide) with h762 | h762
          · rcases m.htr 1 2 3 (by decide) (by decide) with h763 | h763
            · rcases m.htr 1 2 4 (by decide) (by decide) with h764 | h764
              · linarith only [h0, h4, h764, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
                  · linarith only [h1, h759, h767, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h769 | h769
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h770 | h770
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h771 | h771
                        · linarith only [h0, h4, h759, h763, h771, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h3, h4, h771, hc23, hlam, hphi, u3elo3]
                      · linarith only [h759, h762, h763, h764, h770, hc23, hlam, hphi, u3elo3]
                    · linarith only [h759, h761, h769, hc13, hlam, hphi, u3elo3]
                · linarith only [h4, h758, h759, h763, h766, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h759, h763, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h3, h4, h759, h761, h762, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h779 | h779
          · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
            · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
              · linarith only [h0, h4, h781, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h783 | h783
                · rcases m.htr 1 3 4 (by decide) (by decide) with h784 | h784
                  · linarith only [h759, h784, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h786 | h786
                    · linarith only [h1, h761, h786, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
                        · linarith only [h0, h4, h759, h780, h789, hlam]
                        · linarith only [h0, h4, h780, h789, hc23, hlam, hphi, u3elo3]
                      · linarith only [h759, h779, h780, h781, h788, hc23, hlam, hphi, u3elo3]
                · linarith only [h4, h758, h780, h783, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3, h4, h759, h780, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h4, h758, h779, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h796 | h796
      · linarith only [h3, h4, h796, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h798 | h798
        · linarith only [h3, h758, h798, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h800 | h800
          · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
            · rcases m.htr 1 2 4 (by decide) (by decide) with h802 | h802
              · linarith only [h0, h4, h802, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                · linarith only [h0, h758, h804, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
                  · linarith only [h796, h806, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                    · linarith only [h0, h1, h758, h798, h801, h808, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                        · linarith only [h0, h1, h4, h796, h801, h811, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h3, h4, h811, hc23, hlam, hphi, u3elo3]
                      · linarith only [h796, h800, h801, h802, h810, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h801, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h816 | h816
            · rcases m.htr 1 2 4 (by decide) (by decide) with h817 | h817
              · linarith only [h0, h4, h817, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h819 | h819
                · linarith only [h0, h758, h819, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                  · linarith only [h1, h796, h821, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h823 | h823
                    · linarith only [h0, h1, h4, h796, h798, h800, h816, h823, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h825 | h825
                      · linarith only [h0, h4, h800, h816, h821, h825, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h827 | h827
                        · linarith only [h0, h1, h758, h796, h816, h827, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h3, h4, h827, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h816, hc12, hc24, hlam, hphi]

end R2N4
