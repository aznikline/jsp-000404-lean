import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4555 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4556 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5097 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 1 2 3 (by decide) (by decide) with h5256 | h5256
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5257 | h5257
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5258 | h5258
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5259 | h5259
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5260 | h5260
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5261 | h5261
            · linarith only [h4553, h4556, h5261, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5263 | h5263
              · linarith only [h4554, h5097, h5263, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5265 | h5265
                · linarith only [h4553, h5097, h5260, h5265, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases h2bigk with h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c | h5267c
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h0, hlam, p5267_1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5260, hc34, hlam, hphi, ht0b, ht45, ht5b, p5267_1, u0elo1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    rcases p5267_3 (m.d 0 2) (by simp) with h5271 | h5271
                    · rcases p5267_3 (m.d 1 2) (by simp) with h5272 | h5272
                      · rcases p5267_3 (m.d 2 3) (by simp) with h5273 | h5273
                        · linarith only [h4553, h5273, hlam]
                        · linarith only [h5260, h5273, hlam]
                      · linarith only [h5257, h5272, hlam]
                    · linarith only [h5271, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5260, h5261, hc34, hlam, hphi, ht0b, ht45, ht5b, p5267_1, u0elo1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4553, h5260, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5267_1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    rcases p5267_3 (m.d 0 2) (by simp) with h5281 | h5281
                    · linarith only [h0, h5281, hlam]
                    · linarith only [h4553, h5281, hlam]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    rcases p5267_3 (m.d 0 2) (by simp) with h5284 | h5284
                    · linarith only [h0, h5284, hlam]
                    · linarith only [h4554, h5284, hlam]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    rcases p5267_3 (m.d 0 2) (by simp) with h5287 | h5287
                    · linarith only [h0, h5287, hlam]
                    · linarith only [h4555, h5287, hlam]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4553, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5256, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4555, h5261, hc24, hlam, hphi, ht0b, ht45, ht5b, p5267_1, u0elo1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5261, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4554, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5257, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5260, hlam, p5267_1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5263, hlam, p5267_1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4555, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h5258, hlam, p5267_0]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5267_1, u0elo1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [h4555, h5260, hc34, hlam, hphi, ht0b, ht45, ht5b, p5267_1, u0elo1]
                  · have p5267_0 := h5267c.1
                    have p5267_1 := h5267c.2.1
                    have p5267_2 := h5267c.2.2.1
                    have p5267_3 := h5267c.2.2.2
                    linarith only [hlam, p5267_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5305 | h5305
            · linarith only [h4553, h4556, h5305, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5307 | h5307
              · linarith only [h4554, h5097, h5307, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5309 | h5309
                · rcases h2bigk with h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h0, hlam, p5310_1]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5313 | h5313
                    · rcases p5310_3 (m.d 1 2) (by simp) with h5314 | h5314
                      · rcases p5310_3 (m.d 2 3) (by simp) with h5315 | h5315
                        · linarith only [h5315, hlam, p5310_0]
                        · rcases p5310_3 (m.d 2 4) (by simp) with h5317 | h5317
                          · linarith only [h4554, h5317, hlam]
                          · linarith only [h5260, h5317, hlam]
                      · linarith only [h5256, h5314, hlam]
                    · linarith only [h5313, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5322 | h5322
                    · rcases p5310_3 (m.d 1 2) (by simp) with h5323 | h5323
                      · rcases p5310_3 (m.d 2 3) (by simp) with h5324 | h5324
                        · linarith only [h4553, h5324, hlam]
                        · rcases p5310_3 (m.d 2 4) (by simp) with h5326 | h5326
                          · linarith only [h5326, hlam, p5310_0]
                          · rcases p5310_3 (m.d 2 5) (by simp) with h5328 | h5328
                            · linarith only [h4555, h5328, hlam]
                            · linarith only [h5307, h5328, hlam]
                      · linarith only [h5257, h5323, hlam]
                    · linarith only [h5322, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5333 | h5333
                    · rcases p5310_3 (m.d 1 2) (by simp) with h5334 | h5334
                      · rcases p5310_3 (m.d 2 3) (by simp) with h5335 | h5335
                        · linarith only [h4553, h5335, hlam]
                        · rcases p5310_3 (m.d 2 4) (by simp) with h5337 | h5337
                          · linarith only [h4554, h5337, hlam]
                          · rcases p5310_3 (m.d 2 5) (by simp) with h5339 | h5339
                            · linarith only [h5339, hlam, p5310_0]
                            · rcases h5bigk with h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c | h5341c
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [hlam, p5341_0]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h2858, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5097, h5260, h5307, h5309, hc23, hc34, hlam, hphi, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h4556, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5097, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h2858, h5257, h5259, hc01, hc12, hlam, hphi, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [hlam, p5341_0]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                rcases p5341_3 (m.d 0 5) (by simp) with h5349 | h5349
                                · linarith only [h2858, h5349, hlam]
                                · linarith only [h4555, h5349, hlam]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h4554, h5097, h5257, h5259, h5260, h5309, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h4554, h5097, h5257, h5259, h5260, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h4555, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5258, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [hlam, p5341_0]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5305, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5307, hlam, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h2858, h5309, hc01, hc34, hlam, hphi, ht12, ht23, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5260, h5307, h5309, hc23, hc34, hlam, hphi, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [hlam, p5341_0]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h4554, h5097, h5260, h5309, hc23, hc34, hlam, hphi, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h2858, h5259, hc01, hc15, hlam, hphi, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5259, hlam, p5341_0]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5257, h5259, h5260, h5307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5341_1]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [h5309, hlam, p5341_0]
                              · have p5341_0 := h5341c.1
                                have p5341_1 := h5341c.2.1
                                have p5341_2 := h5341c.2.2.1
                                have p5341_3 := h5341c.2.2.2
                                linarith only [hlam, p5341_0]
                      · linarith only [h5258, h5334, hlam]
                    · linarith only [h5333, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5371 | h5371
                    · linarith only [h0, h5371, hlam]
                    · rcases p5310_3 (m.d 1 2) (by simp) with h5373 | h5373
                      · rcases p5310_3 (m.d 2 3) (by simp) with h5374 | h5374
                        · linarith only [h5256, h5374, hlam]
                        · rcases p5310_3 (m.d 2 4) (by simp) with h5376 | h5376
                          · linarith only [h5257, h5376, hlam]
                          · rcases p5310_3 (m.d 2 5) (by simp) with h5378 | h5378
                            · linarith only [h5258, h5378, hlam]
                            · rcases h5bigk with h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [hlam, p5380_0]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h2858, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5260, h5307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5380_1, u0elo4]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h4556, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5097, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h2858, h5257, h5259, hc01, hc12, hlam, hphi, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [hlam, p5380_0]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                rcases p5380_3 (m.d 0 5) (by simp) with h5388 | h5388
                                · linarith only [h2858, h5388, hlam]
                                · linarith only [h4555, h5388, hlam]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h4553, h4556, h5257, h5259, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h4554, h5097, h5257, h5259, h5260, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h4555, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5258, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [hlam, p5380_0]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5305, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5307, hlam, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h2858, h4555, h5260, h5307, h5309, hc01, hc12, hc23, hc34, hlam, hphi, p5310_1, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5260, h5307, h5309, hc23, hc34, hlam, hphi, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [hlam, p5380_0]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h4554, h5097, h5260, h5309, hc23, hc34, hlam, hphi, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h2858, h4555, h5260, h5307, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5310_1, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5259, hlam, p5380_0]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5257, h5259, h5260, h5307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [h5309, hlam, p5380_0]
                              · have p5380_0 := h5380c.1
                                have p5380_1 := h5380c.2.1
                                have p5380_2 := h5380c.2.2.1
                                have p5380_3 := h5380c.2.2.2
                                linarith only [hlam, p5380_0]
                      · linarith only [h0, h5373, hlam]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5410 | h5410
                    · linarith only [h0, h5410, hlam]
                    · linarith only [h4553, h5410, hlam]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5413 | h5413
                    · linarith only [h0, h5413, hlam]
                    · linarith only [h4554, h5413, hlam]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    rcases p5310_3 (m.d 0 2) (by simp) with h5416 | h5416
                    · linarith only [h0, h5416, hlam]
                    · linarith only [h4555, h5416, hlam]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h4553, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h5256, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h5260, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h5305, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h4554, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h5257, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h4555, h5307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5310_1, u0elo1]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h5307, hlam, p5310_1]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h4555, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h5258, hlam, p5310_0]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5310_1, u0elo1]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [h4555, hc24, hlam, hphi, ht0b, ht45, ht5b, p5310_1, u0elo1]
                  · have p5310_0 := h5310c.1
                    have p5310_1 := h5310c.2.1
                    have p5310_2 := h5310c.2.2.1
                    have p5310_3 := h5310c.2.2.2
                    linarith only [hlam, p5310_0]
                · rcases h2bigk with h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c | h5434c
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h0, hlam, p5434_1]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    rcases p5434_3 (m.d 0 2) (by simp) with h5437 | h5437
                    · rcases p5434_3 (m.d 1 2) (by simp) with h5438 | h5438
                      · rcases p5434_3 (m.d 2 3) (by simp) with h5439 | h5439
                        · linarith only [h5439, hlam, p5434_0]
                        · rcases p5434_3 (m.d 2 4) (by simp) with h5441 | h5441
                          · linarith only [h4554, h5441, hlam]
                          · linarith only [h5260, h5441, hlam]
                      · linarith only [h5256, h5438, hlam]
                    · linarith only [h5437, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    rcases p5434_3 (m.d 0 2) (by simp) with h5446 | h5446
                    · rcases p5434_3 (m.d 1 2) (by simp) with h5447 | h5447
                      · rcases p5434_3 (m.d 2 3) (by simp) with h5448 | h5448
                        · linarith only [h4553, h5448, hlam]
                        · rcases p5434_3 (m.d 2 4) (by simp) with h5450 | h5450
                          · linarith only [h5450, hlam, p5434_0]
                          · rcases p5434_3 (m.d 2 5) (by simp) with h5452 | h5452
                            · linarith only [h4555, h5452, hlam]
                            · linarith only [h5307, h5452, hlam]
                      · linarith only [h5257, h5447, hlam]
                    · linarith only [h5446, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    rcases p5434_3 (m.d 0 2) (by simp) with h5457 | h5457
                    · rcases p5434_3 (m.d 1 2) (by simp) with h5458 | h5458
                      · rcases p5434_3 (m.d 2 3) (by simp) with h5459 | h5459
                        · linarith only [h4553, h5459, hlam]
                        · rcases p5434_3 (m.d 2 4) (by simp) with h5461 | h5461
                          · linarith only [h4554, h5461, hlam]
                          · rcases p5434_3 (m.d 2 5) (by simp) with h5463 | h5463
                            · linarith only [h5463, hlam, p5434_0]
                            · rcases h5bigk with h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [hlam, p5465_0]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h2858, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [hc25, hlam, hphi, ht0b, ht5b, p5465_1, u0elo4]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h4556, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5097, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h2858, hc01, hc15, hlam, hphi, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [hlam, p5465_0]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                rcases p5465_3 (m.d 0 5) (by simp) with h5473 | h5473
                                · linarith only [h2858, h5473, hlam]
                                · linarith only [h4555, h5473, hlam]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h4553, h4556, h5257, h5259, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5257, h5259, h5260, h5309, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h4555, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5258, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [hlam, p5465_0]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5305, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5307, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5257, h5259, h5260, h5307, h5309, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [hlam, p5465_0]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5309, hlam, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h2858, h5257, h5259, hc01, hc12, hlam, hphi, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5259, hlam, p5465_0]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5257, h5259, h5260, h5307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [h5257, h5259, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5465_1]
                              · have p5465_0 := h5465c.1
                                have p5465_1 := h5465c.2.1
                                have p5465_2 := h5465c.2.2.1
                                have p5465_3 := h5465c.2.2.2
                                linarith only [hlam, p5465_0]
                      · linarith only [h5258, h5458, hlam]
                    · linarith only [h5457, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    rcases p5434_3 (m.d 0 2) (by simp) with h5495 | h5495
                    · linarith only [h0, h5495, hlam]
                    · rcases p5434_3 (m.d 1 2) (by simp) with h5497 | h5497
                      · rcases p5434_3 (m.d 2 3) (by simp) with h5498 | h5498
                        · linarith only [h5256, h5498, hlam]
                        · rcases p5434_3 (m.d 2 4) (by simp) with h5500 | h5500
                          · linarith only [h5257, h5500, hlam]
                          · rcases p5434_3 (m.d 2 5) (by simp) with h5502 | h5502
                            · linarith only [h5258, h5502, hlam]
                            · rcases h5bigk with h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c | h5504c
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [hlam, p5504_0]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h2858, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5260, h5307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5504_1, u0elo4]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h4556, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5097, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h2858, hc01, hc15, hlam, hphi, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [hlam, p5504_0]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                rcases p5504_3 (m.d 0 5) (by simp) with h5512 | h5512
                                · linarith only [h2858, h5512, hlam]
                                · linarith only [h4555, h5512, hlam]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h4553, h4556, h5257, h5259, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5097, h5257, h5259, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h4555, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5258, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [hlam, p5504_0]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5305, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5307, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h2858, h4555, h5260, h5307, hc01, hc12, hc23, hc35, hlam, hphi, p5434_1, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5260, h5307, hc23, hc35, hlam, hphi, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [hlam, p5504_0]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5309, hlam, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h2858, h4555, h5260, h5307, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5434_1, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5259, hlam, p5504_0]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5257, h5259, h5260, h5307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [h5257, h5259, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5504_1]
                              · have p5504_0 := h5504c.1
                                have p5504_1 := h5504c.2.1
                                have p5504_2 := h5504c.2.2.1
                                have p5504_3 := h5504c.2.2.2
                                linarith only [hlam, p5504_0]
                      · linarith only [h0, h5497, hlam]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5257, h5259, h5260, h5309, hlam, p5434_2]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    rcases p5434_3 (m.d 0 2) (by simp) with h5535 | h5535
                    · linarith only [h0, h5535, hlam]
                    · linarith only [h4554, h5535, hlam]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    rcases p5434_3 (m.d 0 2) (by simp) with h5538 | h5538
                    · linarith only [h0, h5538, hlam]
                    · linarith only [h4555, h5538, hlam]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h4553, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5256, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5260, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5305, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h4554, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5257, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h4555, h5307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5434_1, u0elo1]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5307, hlam, p5434_1]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h4555, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h5258, hlam, p5434_0]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5434_1, u0elo1]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [h4555, hc24, hlam, hphi, ht0b, ht45, ht5b, p5434_1, u0elo1]
                  · have p5434_0 := h5434c.1
                    have p5434_1 := h5434c.2.1
                    have p5434_2 := h5434c.2.2.1
                    have p5434_3 := h5434c.2.2.2
                    linarith only [hlam, p5434_0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5556 | h5556
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5557 | h5557
            · linarith only [h4553, h4556, h5557, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5559 | h5559
              · linarith only [h4554, h5097, h5559, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5561 | h5561
                · linarith only [h4555, h5097, h5556, h5557, h5561, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases h2bigk with h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h0, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5556, hc34, hlam, hphi, ht0b, ht45, ht5b, p5563_1, u0elo1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 2) (by simp) with h5567 | h5567
                    · rcases p5563_3 (m.d 1 2) (by simp) with h5568 | h5568
                      · rcases p5563_3 (m.d 2 3) (by simp) with h5569 | h5569
                        · linarith only [h4553, h5569, hlam]
                        · linarith only [h5556, h5569, hlam]
                      · linarith only [h5257, h5568, hlam]
                    · linarith only [h5567, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5556, h5557, hc34, hlam, hphi, ht0b, ht45, ht5b, p5563_1, u0elo1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4553, h5556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 2) (by simp) with h5577 | h5577
                    · linarith only [h0, h5577, hlam]
                    · linarith only [h4553, h5577, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 2) (by simp) with h5580 | h5580
                    · linarith only [h0, h5580, hlam]
                    · linarith only [h4554, h5580, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 2) (by simp) with h5583 | h5583
                    · linarith only [h0, h5583, hlam]
                    · linarith only [h4555, h5583, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4553, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5256, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4555, h5556, h5557, hc34, hlam, hphi, ht0b, ht45, ht5b, p5563_1, u0elo1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5557, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4554, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5257, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5556, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5559, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4555, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5258, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1, u0elo1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4555, h5556, hc34, hlam, hphi, ht0b, ht45, ht5b, p5563_1, u0elo1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5601 | h5601
            · linarith only [h4553, h4556, h5601, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5603 | h5603
              · linarith only [h4554, h5259, h5603, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5605 | h5605
                · rcases h2bigk with h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h0, hlam, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5609 | h5609
                    · rcases p5606_3 (m.d 1 2) (by simp) with h5610 | h5610
                      · rcases p5606_3 (m.d 2 3) (by simp) with h5611 | h5611
                        · linarith only [h5611, hlam, p5606_0]
                        · rcases p5606_3 (m.d 2 4) (by simp) with h5613 | h5613
                          · linarith only [h4554, h5613, hlam]
                          · linarith only [h5556, h5613, hlam]
                      · linarith only [h5256, h5610, hlam]
                    · linarith only [h5609, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5618 | h5618
                    · rcases p5606_3 (m.d 1 2) (by simp) with h5619 | h5619
                      · rcases p5606_3 (m.d 2 3) (by simp) with h5620 | h5620
                        · linarith only [h4553, h5620, hlam]
                        · rcases p5606_3 (m.d 2 4) (by simp) with h5622 | h5622
                          · linarith only [h5622, hlam, p5606_0]
                          · rcases p5606_3 (m.d 2 5) (by simp) with h5624 | h5624
                            · linarith only [h4555, h5624, hlam]
                            · linarith only [h5603, h5624, hlam]
                      · linarith only [h5257, h5619, hlam]
                    · linarith only [h5618, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5629 | h5629
                    · rcases p5606_3 (m.d 1 2) (by simp) with h5630 | h5630
                      · rcases p5606_3 (m.d 2 3) (by simp) with h5631 | h5631
                        · linarith only [h4553, h5631, hlam]
                        · rcases p5606_3 (m.d 2 4) (by simp) with h5633 | h5633
                          · linarith only [h4554, h5633, hlam]
                          · rcases p5606_3 (m.d 2 5) (by simp) with h5635 | h5635
                            · linarith only [h5635, hlam, p5606_0]
                            · rcases h5bigk with h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [hlam, p5637_0]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h2858, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5556, h5603, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5637_1, u0elo4]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h4556, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5097, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h2858, hc01, hc15, hlam, hphi, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [hlam, p5637_0]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5259, h5556, h5603, h5605, hc23, hc34, hlam, hphi, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5259, h5605, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5259, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h4555, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5258, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [hlam, p5637_0]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5601, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5603, hlam, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h2858, h5605, hc01, hc34, hlam, hphi, ht12, ht23, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5556, h5603, h5605, hc23, hc34, hlam, hphi, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [hlam, p5637_0]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h4554, h5097, h5556, h5605, hc23, hc34, hlam, hphi, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5556, h5603, hc23, hc45, hlam, hphi, ht34, p5637_1]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [h5605, hlam, p5637_0]
                              · have p5637_0 := h5637c.1
                                have p5637_1 := h5637c.2.1
                                have p5637_2 := h5637c.2.2.1
                                have p5637_3 := h5637c.2.2.2
                                linarith only [hlam, p5637_0]
                      · linarith only [h5258, h5630, hlam]
                    · linarith only [h5629, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5665 | h5665
                    · linarith only [h0, h5665, hlam]
                    · rcases p5606_3 (m.d 1 2) (by simp) with h5667 | h5667
                      · rcases p5606_3 (m.d 2 3) (by simp) with h5668 | h5668
                        · linarith only [h5256, h5668, hlam]
                        · rcases p5606_3 (m.d 2 4) (by simp) with h5670 | h5670
                          · linarith only [h5257, h5670, hlam]
                          · rcases p5606_3 (m.d 2 5) (by simp) with h5672 | h5672
                            · linarith only [h5258, h5672, hlam]
                            · rcases h5bigk with h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c | h5674c
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [hlam, p5674_0]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h2858, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5556, h5603, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5674_1, u0elo4]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h4556, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5097, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h2858, hc01, hc15, hlam, hphi, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [hlam, p5674_0]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5259, h5556, h5603, h5605, hc23, hc34, hlam, hphi, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5259, h5605, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5259, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h4555, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5258, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [hlam, p5674_0]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5601, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5603, hlam, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, hc01, hc12, hc23, hc35, hlam, hphi, p5606_1, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, h5605, hc01, hc12, hc23, hc34, hlam, hphi, p5606_1, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5556, h5603, h5605, hc23, hc34, hlam, hphi, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [hlam, p5674_0]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h4554, h5097, h5556, h5605, hc23, hc34, hlam, hphi, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5606_1, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5606_1, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5556, h5603, hc23, hc45, hlam, hphi, ht34, p5674_1]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [h5605, hlam, p5674_0]
                              · have p5674_0 := h5674c.1
                                have p5674_1 := h5674c.2.1
                                have p5674_2 := h5674c.2.2.1
                                have p5674_3 := h5674c.2.2.2
                                linarith only [hlam, p5674_0]
                      · linarith only [h0, h5667, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5702 | h5702
                    · linarith only [h0, h5702, hlam]
                    · linarith only [h4553, h5702, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5705 | h5705
                    · linarith only [h0, h5705, hlam]
                    · linarith only [h4554, h5705, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 2) (by simp) with h5708 | h5708
                    · linarith only [h0, h5708, hlam]
                    · linarith only [h4555, h5708, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4553, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5256, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5556, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5601, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4554, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5257, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4555, h5603, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5606_1, u0elo1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5603, hlam, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4555, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5258, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5606_1, u0elo1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4555, hc24, hlam, hphi, ht0b, ht45, ht5b, p5606_1, u0elo1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                · rcases h2bigk with h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c | h5726c
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h0, hlam, p5726_1]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5729 | h5729
                    · rcases p5726_3 (m.d 1 2) (by simp) with h5730 | h5730
                      · rcases p5726_3 (m.d 2 3) (by simp) with h5731 | h5731
                        · linarith only [h5731, hlam, p5726_0]
                        · rcases p5726_3 (m.d 2 4) (by simp) with h5733 | h5733
                          · linarith only [h4554, h5733, hlam]
                          · linarith only [h5556, h5733, hlam]
                      · linarith only [h5256, h5730, hlam]
                    · linarith only [h5729, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5738 | h5738
                    · rcases p5726_3 (m.d 1 2) (by simp) with h5739 | h5739
                      · rcases p5726_3 (m.d 2 3) (by simp) with h5740 | h5740
                        · linarith only [h4553, h5740, hlam]
                        · rcases p5726_3 (m.d 2 4) (by simp) with h5742 | h5742
                          · linarith only [h5742, hlam, p5726_0]
                          · rcases p5726_3 (m.d 2 5) (by simp) with h5744 | h5744
                            · linarith only [h4555, h5744, hlam]
                            · linarith only [h5603, h5744, hlam]
                      · linarith only [h5257, h5739, hlam]
                    · linarith only [h5738, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5749 | h5749
                    · rcases p5726_3 (m.d 1 2) (by simp) with h5750 | h5750
                      · rcases p5726_3 (m.d 2 3) (by simp) with h5751 | h5751
                        · linarith only [h4553, h5751, hlam]
                        · rcases p5726_3 (m.d 2 4) (by simp) with h5753 | h5753
                          · linarith only [h4554, h5753, hlam]
                          · rcases p5726_3 (m.d 2 5) (by simp) with h5755 | h5755
                            · linarith only [h5755, hlam, p5726_0]
                            · rcases h5bigk with h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [hlam, p5757_0]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h2858, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [hc25, hlam, hphi, ht0b, ht5b, p5757_1, u0elo4]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h4556, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5097, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h2858, hc01, hc15, hlam, hphi, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [hlam, p5757_0]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5259, h5601, hc23, hc45, hlam, hphi, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h4553, h4556, h5259, hc23, hc45, hlam, hphi, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5259, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h4555, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5258, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [hlam, p5757_0]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5601, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5603, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h2858, h5605, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5556, h5603, h5605, hc23, hc45, hlam, hphi, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [hlam, p5757_0]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5605, hlam, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h5556, h5603, hc23, hc45, hlam, hphi, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [h4553, h4556, hc23, hc45, hlam, hphi, ht34, p5757_1]
                              · have p5757_0 := h5757c.1
                                have p5757_1 := h5757c.2.1
                                have p5757_2 := h5757c.2.2.1
                                have p5757_3 := h5757c.2.2.2
                                linarith only [hlam, p5757_0]
                      · linarith only [h5258, h5750, hlam]
                    · linarith only [h5749, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5785 | h5785
                    · linarith only [h0, h5785, hlam]
                    · rcases p5726_3 (m.d 1 2) (by simp) with h5787 | h5787
                      · rcases p5726_3 (m.d 2 3) (by simp) with h5788 | h5788
                        · linarith only [h5256, h5788, hlam]
                        · rcases p5726_3 (m.d 2 4) (by simp) with h5790 | h5790
                          · linarith only [h5257, h5790, hlam]
                          · rcases p5726_3 (m.d 2 5) (by simp) with h5792 | h5792
                            · linarith only [h5258, h5792, hlam]
                            · rcases h5bigk with h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c | h5794c
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [hlam, p5794_0]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h2858, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5556, h5603, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5794_1, u0elo4]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h4556, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5097, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h2858, hc01, hc15, hlam, hphi, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [hlam, p5794_0]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5259, h5556, h5603, hc23, hc45, hlam, hphi, ht34, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h4553, h4556, h5259, hc23, hc45, hlam, hphi, ht34, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5259, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h4555, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5258, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [hlam, p5794_0]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5601, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5603, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, h5605, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5726_1, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5556, h5603, h5605, hc23, hc45, hlam, hphi, ht34, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [hlam, p5794_0]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5605, hlam, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5726_1, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h2858, h4555, h5556, h5603, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p5726_1, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h5556, h5603, hc23, hc45, hlam, hphi, ht34, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [h4553, h4556, hc23, hc45, hlam, hphi, ht34, p5794_1]
                              · have p5794_0 := h5794c.1
                                have p5794_1 := h5794c.2.1
                                have p5794_2 := h5794c.2.2.1
                                have p5794_3 := h5794c.2.2.2
                                linarith only [hlam, p5794_0]
                      · linarith only [h0, h5787, hlam]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5822 | h5822
                    · linarith only [h0, h5822, hlam]
                    · linarith only [h4553, h5822, hlam]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5825 | h5825
                    · linarith only [h0, h5825, hlam]
                    · linarith only [h4554, h5825, hlam]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    rcases p5726_3 (m.d 0 2) (by simp) with h5828 | h5828
                    · linarith only [h0, h5828, hlam]
                    · linarith only [h4555, h5828, hlam]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h4553, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h5256, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h5556, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h5601, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h4554, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h5257, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h4555, h5603, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5726_1, u0elo1]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h5603, hlam, p5726_1]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h4555, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h5258, hlam, p5726_0]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5726_1, u0elo1]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [h4555, hc24, hlam, hphi, ht0b, ht45, ht5b, p5726_1, u0elo1]
                  · have p5726_0 := h5726c.1
                    have p5726_1 := h5726c.2.1
                    have p5726_2 := h5726c.2.2.1
                    have p5726_3 := h5726c.2.2.2
                    linarith only [hlam, p5726_0]
      · linarith only [h0, h4555, h5258, hlam]
    · linarith only [h0, h4554, h5257, hlam]
  · linarith only [h0, h4553, h4556, h5256, hc01, hc35, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4555 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4556 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 4 5 (by decide) (by decide) with h5097 | h5097
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x1_x0 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554 h4555 h4556 h5097
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x1_x1 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554 h4555 h4556 h5097

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4555 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 3 5 (by decide) (by decide) with h4556 | h4556
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554 h4555 h4556
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554 h4555 h4556

end R2N4
