import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4439 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4818 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h5094 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h5095 | h5095
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5096 | h5096
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5097 | h5097
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5098 | h5098
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5099 | h5099
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5100 | h5100
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5101 | h5101
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5102 | h5102
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5103 | h5103
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5104 | h5104
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5105 | h5105
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5106 | h5106
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5107 | h5107
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5108 | h5108
                            · linarith only [h5094, h5105, h5108, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h0, h5094, h5105, h5107, h5108, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5111 | h5111
                            · linarith only [h0, h5094, h5105, h5107, h5111, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases h0bigk with h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, hlam, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h3888, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4439, hlam, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4818, hlam, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h5099, h5105, h5107, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h3888, h5100, hc01, hlam, hphi, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5094, hlam, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h3888, h4439, h5100, hc01, hlam, hphi, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h3888, h5099, h5100, h5105, h5107, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4439, h5100, h5102, hc01, hlam, hphi, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5095, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5097, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4439, h5099, h5100, h5102, h5105, h5107, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5113_1, u1elo1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5113_1, u1elo4]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5096, hlam, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5098, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5099, hlam, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                        · linarith only [h3888, h5098, h5100, h5105, h5106, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5140 | h5140
                        · linarith only [h3888, h5097, h5100, h5105, h5140, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5142 | h5142
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5143 | h5143
                            · rcases h0bigk with h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c | h5144c
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h0, hlam, p5144_1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h3888, hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h4439, hlam, p5144_1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h4818, hlam, p5144_1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h0, h5097, h5140, h5143, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h3888, h5100, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h5094, hlam, p5144_1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h3888, h5095, h5100, h5142, hc45, hlam, hphi, ht01, ht0b, ht5b, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h3888, h4818, h5100, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h4439, h5100, h5102, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h5095, hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h5097, hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h4439, h5098, h5100, h5102, h5140, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h4818, h5100, h5102, h5104, hc01, hlam, hphi, p5144_1, u1elo1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h5096, hlam, p5144_1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h5098, hlam, p5144_0]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [h5099, hlam, p5144_1]
                              · have p5144_0 := h5144c.1
                                have p5144_1 := h5144c.2.1
                                have p5144_2 := h5144c.2.2.1
                                have p5144_3 := h5144c.2.2.2
                                linarith only [hlam, p5144_0]
                            · linarith only [h0, h5095, h5142, h5143, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5171 | h5171
                            · linarith only [h3888, h5097, h5100, h5142, h5171, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h4439, h5099, h5100, h5102, h5105, h5171, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h4439, h5099, h5104, hlam]
                  · linarith only [h3888, h5098, h5103, hlam]
                · linarith only [h3888, h5097, h5102, hlam]
              · linarith only [h0, h5095, h5101, hlam]
            · linarith only [h0, h5094, h5100, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5179 | h5179
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5180 | h5180
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5181 | h5181
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5182 | h5182
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5183 | h5183
                    · linarith only [h4439, h5099, h5183, hc01, hlam, hphi, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5185 | h5185
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5186 | h5186
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5187 | h5187
                          · linarith only [h4439, h5095, h5183, h5187, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5189 | h5189
                            · linarith only [h4439, h5183, h5189, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c | h5191c
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h0, hlam, p5191_1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h3888, hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h4439, hlam, p5191_1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h4818, hlam, p5191_1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h0, h4439, h5099, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h3888, h5179, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h5094, hlam, p5191_1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h3888, h4439, h5179, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h3888, h4439, h5099, h5179, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5191_1, u1elo3]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h5095, hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h5097, hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h5099, hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5191_1, u1elo4]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h5096, hlam, p5191_1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h5098, hlam, p5191_0]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [h3888, h4439, h5098, h5179, hc01, hlam, hphi, p5191_1, u1elo1]
                              · have p5191_0 := h5191c.1
                                have p5191_1 := h5191c.2.1
                                have p5191_2 := h5191c.2.2.1
                                have p5191_3 := h5191c.2.2.2
                                linarith only [hlam, p5191_0]
                        · linarith only [h3888, h5098, h5179, h5185, h5186, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5218 | h5218
                        · linarith only [h3888, h5097, h5179, h5185, h5218, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5220 | h5220
                          · linarith only [h4439, h5183, h5220, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5222 | h5222
                            · linarith only [h3888, h4439, h5097, h5179, h5183, h5222, hc01, hlam, hphi, u1elo1]
                            · rcases h0bigk with h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h0, hlam, p5224_1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h3888, hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h4439, hlam, p5224_1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h4818, hlam, p5224_1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h0, h5098, h5185, h5222, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h0, h5097, h5185, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h3888, h5179, hc01, hlam, hphi, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h5094, hlam, p5224_1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h3888, h5097, h5179, h5185, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h3888, h4818, h5179, hc01, hlam, hphi, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5224_1, u1elo3]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h5095, hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h5097, hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h5099, hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h4818, h5179, h5182, hc01, hlam, hphi, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h5096, hlam, p5224_1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h5098, hlam, p5224_0]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [h4439, h4818, h5179, h5182, hc01, hlam, hphi, p5224_1, u1elo1]
                              · have p5224_0 := h5224c.1
                                have p5224_1 := h5224c.2.1
                                have p5224_2 := h5224c.2.2.1
                                have p5224_3 := h5224c.2.2.2
                                linarith only [hlam, p5224_0]
                  · linarith only [h3888, h5098, h5182, hlam]
                · linarith only [h3888, h4439, h5097, h5181, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h3888, h5095, h5098, h5099, h5180, hc01, hlam, hphi, u1elo2]
            · linarith only [h0, h5094, h5179, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5254 | h5254
          · linarith only [h5097, h5098, h5254, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5256 | h5256
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5257 | h5257
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5258 | h5258
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5259 | h5259
                  · linarith only [h5097, h5098, h5256, h5259, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5261 | h5261
                    · linarith only [h4439, h5254, h5258, h5259, h5261, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5263 | h5263
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5264 | h5264
                        · linarith only [h3888, h5094, h5259, h5264, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5266 | h5266
                          · linarith only [h4439, h5095, h5261, h5266, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5268 | h5268
                            · linarith only [h4439, h5094, h5261, h5263, h5268, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c | h5270c
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, hlam, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h3888, hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h4439, hlam, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h4818, hlam, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5270_1, u1elo1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5270_1, u1elo1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5270_1, u1elo1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5270_1, u1elo1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h3888, h5259, h5268, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h5094, hlam, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h3888, h5259, h5268, hc04, hc45, hlam, hphi, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h5098, hlam, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5270_1, u1elo3]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h5095, hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h5097, hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h5254, hlam, p5270_0]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5270_1, u1elo4]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h5096, hlam, p5270_1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, h3888, h5096, hc01, hlam, hphi, p5270_1, u1elo1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [h0, h4439, h5096, hc01, hlam, hphi, p5270_1, u1elo1]
                              · have p5270_0 := h5270c.1
                                have p5270_1 := h5270c.2.1
                                have p5270_2 := h5270c.2.2.1
                                have p5270_3 := h5270c.2.2.2
                                linarith only [hlam, p5270_0]
                      · linarith only [h3888, h5097, h5259, h5263, hc23, hc35, hlam, hphi]
                · linarith only [h3888, h4439, h5097, h5258, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h5095, h5257, hlam]
            · linarith only [h0, h5094, h5256, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5300 | h5300
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5301 | h5301
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5302 | h5302
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5303 | h5303
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5304 | h5304
                · linarith only [h5097, h5300, h5304, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5306 | h5306
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5307 | h5307
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5308 | h5308
                      · linarith only [h4818, h5094, h5304, h5306, h5308, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5310 | h5310
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5311 | h5311
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5312 | h5312
                            · rcases h0bigk with h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c | h5313c
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h0, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h3888, hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h4439, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h4818, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h3888, h5303, h5304, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h5094, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h5097, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h3888, h4818, h5303, h5304, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h4439, h5303, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h5095, hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h3888, h4439, h5303, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h4439, h4818, h5303, hc01, hlam, hphi, p5313_1, u1elo1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h4818, h5304, h5306, hc01, hc34, hlam, hphi, ht12, ht23, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h5096, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h5300, hlam, p5313_0]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [h5301, hlam, p5313_1]
                              · have p5313_0 := h5313c.1
                                have p5313_1 := h5313c.2.1
                                have p5313_2 := h5313c.2.2.1
                                have p5313_3 := h5313c.2.2.2
                                linarith only [hlam, p5313_0]
                            · linarith only [h3888, h5304, h5312, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h5095, h5301, h5308, h5310, h5311, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h3888, h5300, h5304, h5310, hc23, hc34, hlam, hphi]
                    · linarith only [h4439, h5301, h5307, hlam]
                  · linarith only [h3888, h5300, h5306, hlam]
              · linarith only [h0, h5095, h5303, hlam]
            · linarith only [h0, h5094, h5302, hlam]
          · linarith only [h5097, h5300, h5301, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5347 | h5347
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5348 | h5348
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5349 | h5349
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5350 | h5350
                · linarith only [h3888, h5097, h5350, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5352 | h5352
                  · linarith only [h3888, h5300, h5350, h5352, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5354 | h5354
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5355 | h5355
                      · linarith only [h5094, h5350, h5355, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5357 | h5357
                        · linarith only [h3888, h5094, h5352, h5357, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5359 | h5359
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5360 | h5360
                            · rcases h0bigk with h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c | h5361c
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [hlam, p5361_0]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h0, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h3888, hlam, p5361_0]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h4439, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h4818, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [hlam, p5361_0]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5361_1, u1elo2]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h5094, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [hlam, p5361_0]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h5097, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h5300, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h4439, h5349, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h5095, hlam, p5361_0]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h3888, h4439, h5349, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [hlam, p5361_0]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h4439, h4818, h5349, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h4818, h5349, h5354, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h5096, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h3888, h4818, h5349, h5354, hc01, hlam, hphi, p5361_1, u1elo1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [h5347, hlam, p5361_1]
                              · have p5361_0 := h5361c.1
                                have p5361_1 := h5361c.2.1
                                have p5361_2 := h5361c.2.2.1
                                have p5361_3 := h5361c.2.2.2
                                linarith only [hlam, p5361_0]
                            · linarith only [h0, h5095, h5359, h5360, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5388 | h5388
                            · rcases h0bigk with h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c | h5389c
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [hlam, p5389_0]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h0, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h3888, hlam, p5389_0]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h4439, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h4818, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [hlam, p5389_0]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h0, h5347, h5355, h5359, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5389_1, u1elo2]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h5094, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [hlam, p5389_0]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h5097, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h5300, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h4439, h5349, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h5095, hlam, p5389_0]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h3888, h4439, h5349, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [hlam, p5389_0]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h3888, h4439, h5300, h5349, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h4818, h5349, h5354, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h5096, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h3888, h4818, h5349, h5354, hc01, hlam, hphi, p5389_1, u1elo1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [h5347, hlam, p5389_1]
                              · have p5389_0 := h5389c.1
                                have p5389_1 := h5389c.2.1
                                have p5389_2 := h5389c.2.2.1
                                have p5389_3 := h5389c.2.2.2
                                linarith only [hlam, p5389_0]
                            · linarith only [h5097, h5347, h5388, hlam]
                    · linarith only [h4439, h5347, h5354, hlam]
              · linarith only [h0, h5095, h5349, hlam]
            · linarith only [h0, h5094, h5348, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5419 | h5419
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5420 | h5420
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5421 | h5421
                · linarith only [h3888, h5097, h5421, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5423 | h5423
                  · linarith only [h3888, h5300, h5421, h5423, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5425 | h5425
                    · linarith only [h4439, h5347, h5420, h5425, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5427 | h5427
                      · linarith only [h5094, h5097, h5427, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5429 | h5429
                        · linarith only [h5095, h5423, h5427, h5429, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5431 | h5431
                          · linarith only [h0, h5095, h5425, h5431, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5433 | h5433
                            · linarith only [h3888, h5421, h5425, h5433, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h3888, h5421, h5433, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h5095, h5420, hlam]
            · linarith only [h0, h3888, h5094, h5419, hc01, hlam, hphi, u1elo2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5438 | h5438
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5439 | h5439
        · linarith only [h5094, h5096, h5439, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5441 | h5441
          · linarith only [h5094, h5096, h5438, h5441, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5443 | h5443
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5444 | h5444
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5445 | h5445
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5446 | h5446
                  · linarith only [h5438, h5439, h5443, h5446, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5448 | h5448
                    · linarith only [h5094, h5096, h5441, h5445, h5446, h5448, hc23, hc35, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5450 | h5450
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5451 | h5451
                        · linarith only [h5094, h5446, h5451, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5453 | h5453
                          · linarith only [h5095, h5441, h5453, hlam]
                          · linarith only [h5094, h5096, h5450, h5453, hc34, hc45, hlam, hphi]
                      · linarith only [h5438, h5439, h5450, hc23, hc35, hlam, hphi]
                · linarith only [h5438, h5439, h5445, hc13, hc35, hlam, hphi]
              · linarith only [h0, h4818, h5095, h5096, h5444, hc01, hlam, hphi, u1elo4]
            · linarith only [h0, h5094, h5443, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5460 | h5460
        · linarith only [h5095, h5096, h5438, h5460, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5462 | h5462
          · linarith only [h5095, h5096, h5462, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5464 | h5464
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5465 | h5465
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5466 | h5466
                · linarith only [h3888, h5438, h5466, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5468 | h5468
                  · linarith only [h3888, h5460, h5466, h5468, hc01, hlam, hphi, u1elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5470 | h5470
                    · linarith only [h4439, h5462, h5465, h5470, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5472 | h5472
                      · linarith only [h5094, h5438, h5472, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5474 | h5474
                        · linarith only [h5095, h5468, h5472, h5474, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5476 | h5476
                          · linarith only [h5095, h5096, h5470, h5474, h5476, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5478 | h5478
                            · linarith only [h5095, h5096, h5472, h5476, h5478, hc23, hc34, hlam, hphi]
                            · linarith only [h3888, h5466, h5478, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h5095, h5096, h5465, hc12, hc25, hlam, hphi]
            · linarith only [h0, h5094, h5464, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5483 | h5483
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5484 | h5484
      · linarith only [h5094, h5095, h5484, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5486 | h5486
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5487 | h5487
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5488 | h5488
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5489 | h5489
              · linarith only [h5094, h5095, h5489, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5491 | h5491
                · linarith only [h5484, h5486, h5491, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5493 | h5493
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5494 | h5494
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5495 | h5495
                      · linarith only [h5094, h5491, h5495, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5497 | h5497
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5498 | h5498
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5499 | h5499
                            · rcases h0bigk with h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c | h5500c
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [hlam, p5500_0]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h0, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h3888, hlam, p5500_0]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h4439, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h4818, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h0, h5489, h5495, hc01, hc34, hlam, hphi, ht12, ht23, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [hlam, p5500_0]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h0, h5094, h5489, h5495, h5497, h5499, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h5095, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h0, h4818, h5489, h5495, hc01, hc34, hlam, hphi, ht12, ht23, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5500_1, u1elo2]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h5094, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [hlam, p5500_0]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h5484, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h0, h4818, h5094, h5489, h5495, hc01, hc34, hlam, hphi, ht12, ht23, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5500_1, u1elo3]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h0, h4439, hc01, hlam, hphi, p5500_1, u1elo3]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h4439, h5094, h5497, h5499, hc45, hlam, hphi, ht01, ht0b, ht5b, p5500_1, u1elo3]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [hlam, p5500_0]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h4439, h4818, hc01, hlam, hphi, p5500_1, u1elo3]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5500_1, u1elo4]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h5483, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h5486, hlam, p5500_0]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [h5487, hlam, p5500_1]
                              · have p5500_0 := h5500c.1
                                have p5500_1 := h5500c.2.1
                                have p5500_2 := h5500c.2.2.1
                                have p5500_3 := h5500c.2.2.2
                                linarith only [hlam, p5500_0]
                            · linarith only [h0, h5489, h5495, h5499, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h4439, h5487, h5489, h5498, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h0, h5094, h5486, h5489, h5495, h5497, hc23, hc34, hlam, hphi]
                    · linarith only [h4439, h5487, h5494, hlam]
                  · linarith only [h3888, h5486, h5493, hlam]
            · linarith only [h0, h5094, h5488, hlam]
          · linarith only [h5094, h5095, h5486, h5487, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5533 | h5533
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5534 | h5534
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5535 | h5535
              · linarith only [h5094, h5095, h5535, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5537 | h5537
                · linarith only [h3888, h5484, h5537, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5539 | h5539
                  · linarith only [h3888, h5486, h5537, h5539, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5541 | h5541
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5542 | h5542
                      · linarith only [h5094, h5537, h5542, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5544 | h5544
                        · linarith only [h3888, h5094, h5539, h5544, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5546 | h5546
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5547 | h5547
                            · rcases h0bigk with h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c | h5548c
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [hlam, p5548_0]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h0, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h3888, hlam, p5548_0]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h4439, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h4818, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h0, h5535, h5542, hc01, hc34, hlam, hphi, ht12, ht23, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [hlam, p5548_0]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h0, h5535, h5542, hc03, hc34, hlam, hphi, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h5095, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h0, h4818, h5535, h5542, hc01, hc34, hlam, hphi, ht12, ht23, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h3888, h5534, h5535, h5542, hc01, hc34, hlam, hphi, ht12, ht23, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h5094, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [hlam, p5548_0]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h5484, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h5486, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5548_1, u1elo3]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h4439, h5483, h5544, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5548_1, u1elo3]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5548_1, u1elo3]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [hlam, p5548_0]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h3888, h4439, h5486, hc01, hlam, hphi, p5548_1, u1elo3]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5548_1, u1elo4]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h5483, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h0, h3888, h5483, h5535, h5542, hc01, hc34, hlam, hphi, ht12, ht23, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [h5533, hlam, p5548_1]
                              · have p5548_0 := h5548c.1
                                have p5548_1 := h5548c.2.1
                                have p5548_2 := h5548c.2.2.1
                                have p5548_3 := h5548c.2.2.2
                                linarith only [hlam, p5548_0]
                            · linarith only [h0, h5535, h5542, h5547, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h5483, h5533, h5535, h5546, hlam]
                    · linarith only [h0, h4439, h5483, h5533, h5541, hc01, hlam, hphi, u1elo1]
            · linarith only [h0, h5094, h5534, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h5095, h5483, h5533, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5579 | h5579
      · linarith only [h5094, h5095, h5579, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5581 | h5581
        · linarith only [h5094, h5483, h5581, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5583 | h5583
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5584 | h5584
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5585 | h5585
              · linarith only [h5094, h5095, h5585, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5587 | h5587
                · linarith only [h3888, h5579, h5584, h5585, h5587, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5589 | h5589
                  · linarith only [h3888, h5581, h5587, h5589, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5591 | h5591
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5592 | h5592
                      · linarith only [h5094, h5587, h5592, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5594 | h5594
                        · linarith only [h3888, h5094, h5589, h5594, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5596 | h5596
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5597 | h5597
                            · rcases h0bigk with h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c | h5598c
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [hlam, p5598_0]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h0, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h3888, hlam, p5598_0]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4439, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4818, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h0, h5585, h5592, hc01, hc34, hlam, hphi, ht12, ht23, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [hlam, p5598_0]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h0, h5585, h5592, hc03, hc34, hlam, hphi, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h5095, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h5483, hlam, p5598_0]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h3888, h5584, h5585, h5592, hc01, hc34, hlam, hphi, ht12, ht23, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h5094, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [hlam, p5598_0]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h5579, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h5581, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5598_1, u1elo3]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4439, h5094, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5598_1, u1elo3]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5598_1, u1elo3]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [hlam, p5598_0]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4439, h4818, hc01, hlam, hphi, p5598_1, u1elo3]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5598_1, u1elo4]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h4818, h5094, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5598_1, u1elo4]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5598_1, u1elo4]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [h5583, hlam, p5598_1]
                              · have p5598_0 := h5598c.1
                                have p5598_1 := h5598c.2.1
                                have p5598_2 := h5598c.2.2.1
                                have p5598_3 := h5598c.2.2.2
                                linarith only [hlam, p5598_0]
                            · linarith only [h4439, h5583, h5585, h5592, h5597, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h3888, h4439, h5583, h5584, h5585, h5596, hc01, hlam, hphi, u1elo3]
                    · linarith only [h4439, h5583, h5591, hlam]
            · linarith only [h0, h5094, h5584, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5628 | h5628
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5629 | h5629
              · linarith only [h0, h5095, h5629, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5631 | h5631
                · linarith only [h3888, h5579, h5631, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5633 | h5633
                  · linarith only [h3888, h5581, h5628, h5629, h5633, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5635 | h5635
                    · linarith only [h4439, h5583, h5635, hc01, hlam, hphi, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5637 | h5637
                      · linarith only [h5094, h5631, h5637, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5639 | h5639
                        · linarith only [h3888, h5094, h5633, h5639, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5641 | h5641
                          · linarith only [h0, h5094, h5629, h5635, h5637, h5641, hc23, hc34, hlam, hphi]
                          · linarith only [h5094, h5095, h5641, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h5094, h5095, h5628, hc12, hc24, hlam, hphi]

end R2N4
