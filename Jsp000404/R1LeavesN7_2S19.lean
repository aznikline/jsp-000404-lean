import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11162000 in
set_option maxHeartbeats 11162000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s10_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7337 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7338 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h7339 | h7339
  · rcases m.htr 0 3 5 (by decide) (by decide) with h7340 | h7340
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7341 | h7341
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7342 | h7342
        · linarith only [h0, h4, h7337, h7342, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7344 | h7344
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7345 | h7345
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7346 | h7346
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7347 | h7347
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7348 | h7348
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7349 | h7349
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7350 | h7350
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7351 | h7351
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7352 | h7352
                          · rcases h0bigk with h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c | h7353c
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h0, h7344, h7349, h7352, hc01, hc45, hlam, hphi, ht0b, ht5b, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h0, h4, h7344, h7349, h7352, hc01, hc45, hlam, hphi, ht0b, ht5b, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              rcases p7353_3 (m.d 0 1) (by simp) with h7357 | h7357
                              · rcases p7353_3 (m.d 0 2) (by simp) with h7358 | h7358
                                · linarith only [h0, h7358, hlam]
                                · linarith only [h7337, h7358, hlam]
                              · linarith only [h2, h7357, hlam]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              rcases p7353_3 (m.d 0 1) (by simp) with h7362 | h7362
                              · rcases p7353_3 (m.d 0 2) (by simp) with h7363 | h7363
                                · linarith only [h0, h7363, hlam]
                                · linarith only [h7338, h7363, hlam]
                              · linarith only [h3, h7362, hlam]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h0, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h4, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h4, h7337, h7349, h7352, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              rcases p7353_3 (m.d 0 1) (by simp) with h7371 | h7371
                              · rcases p7353_3 (m.d 0 2) (by simp) with h7372 | h7372
                                · rcases p7353_3 (m.d 0 3) (by simp) with h7373 | h7373
                                  · rcases p7353_3 (m.d 0 4) (by simp) with h7374 | h7374
                                    · linarith only [h7337, h7374, hlam]
                                    · linarith only [h7341, h7374, hlam]
                                  · linarith only [h7340, h7373, hlam]
                                · linarith only [h7338, h7372, hlam]
                              · linarith only [h3, h7371, hlam]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h1, hlam, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h0, h4, h7344, h7349, h7352, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              rcases p7353_3 (m.d 0 1) (by simp) with h7383 | h7383
                              · rcases p7353_3 (m.d 0 2) (by simp) with h7384 | h7384
                                · linarith only [h4, h7384, hlam]
                                · linarith only [h7337, h7384, hlam]
                              · linarith only [h2, h7383, hlam]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              rcases p7353_3 (m.d 0 1) (by simp) with h7388 | h7388
                              · rcases p7353_3 (m.d 0 2) (by simp) with h7389 | h7389
                                · linarith only [h4, h7389, hlam]
                                · linarith only [h7338, h7389, hlam]
                              · linarith only [h3, h7388, hlam]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h2, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h7337, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h7339, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              rcases p7353_3 (m.d 0 1) (by simp) with h7397 | h7397
                              · rcases p7353_3 (m.d 0 2) (by simp) with h7398 | h7398
                                · rcases p7353_3 (m.d 0 3) (by simp) with h7399 | h7399
                                  · rcases p7353_3 (m.d 0 4) (by simp) with h7400 | h7400
                                    · rcases p7353_3 (m.d 0 5) (by simp) with h7401 | h7401
                                      · linarith only [h7341, h7401, hlam]
                                      · rcases h2bigk with h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c | h7403c
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7344, h7349, h7352, hc02, hc45, hlam, hphi, ht0b, ht5b, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h4, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h4, h7349, h7352, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          rcases p7403_3 (m.d 0 2) (by simp) with h7408 | h7408
                                          · rcases p7403_3 (m.d 1 2) (by simp) with h7409 | h7409
                                            · linarith only [h0, h7409, hlam]
                                            · linarith only [h7345, h7409, hlam]
                                          · linarith only [h7408, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h0, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7342, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h0, h7349, h7352, hc01, hc45, hlam, hphi, ht0b, ht5b, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          rcases p7403_3 (m.d 0 2) (by simp) with h7417 | h7417
                                          · rcases p7403_3 (m.d 1 2) (by simp) with h7418 | h7418
                                            · rcases p7403_3 (m.d 2 3) (by simp) with h7419 | h7419
                                              · rcases p7403_3 (m.d 2 4) (by simp) with h7420 | h7420
                                                · linarith only [h7344, h7420, hlam]
                                                · linarith only [h7351, h7420, hlam]
                                              · linarith only [h7350, h7419, hlam]
                                            · linarith only [h7418, hlam, p7403_0]
                                          · linarith only [h7338, h7417, hlam]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7337, h7349, h7352, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7344, h7349, h7352, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          rcases p7403_3 (m.d 0 2) (by simp) with h7429 | h7429
                                          · linarith only [h4, h7429, hlam]
                                          · linarith only [h7337, h7429, hlam]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h3, h4, h7337, h7345, hlam, p7353_1, p7403_2]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7337, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7344, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7349, hlam, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h0, h7344, h7350, h7352, hc01, hc45, hlam, hphi, ht0b, ht5b, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7338, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7345, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7350, hlam, p7403_1]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [h7351, hlam, p7403_0]
                                        · have p7403_0 := h7403c.1
                                          have p7403_1 := h7403c.2.1
                                          have p7403_2 := h7403c.2.2.1
                                          have p7403_3 := h7403c.2.2.2
                                          linarith only [hlam, p7403_0]
                                    · linarith only [h7341, h7400, hlam]
                                  · linarith only [h7340, h7399, hlam]
                                · linarith only [h7338, h7398, hlam]
                              · linarith only [h3, h7397, hlam]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h3, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h7338, hlam, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h7340, hlam, p7353_0]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [h7341, hlam, p7353_1]
                            · have p7353_0 := h7353c.1
                              have p7353_1 := h7353c.2.1
                              have p7353_2 := h7353c.2.2.1
                              have p7353_3 := h7353c.2.2.2
                              linarith only [hlam, p7353_0]
                          · linarith only [h0, h4, h7344, h7351, h7352, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7453 | h7453
                          · linarith only [h1, h7346, h7351, h7453, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h0bigk with h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c | h7455c
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, h7337, h7348, h7349, h7351, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, h4, h7337, h7348, h7349, h7351, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, h7348, h7349, h7351, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              rcases p7455_3 (m.d 0 1) (by simp) with h7460 | h7460
                              · rcases p7455_3 (m.d 0 2) (by simp) with h7461 | h7461
                                · linarith only [h0, h7461, hlam]
                                · linarith only [h7338, h7461, hlam]
                              · linarith only [h3, h7460, hlam]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h0, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h4, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, h4, h7348, h7349, h7351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h3, h4, h7348, h7349, h7351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h1, hlam, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, h4, h7337, h7348, h7349, h7351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, h4, h7348, h7349, h7351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              rcases p7455_3 (m.d 0 1) (by simp) with h7474 | h7474
                              · rcases p7455_3 (m.d 0 2) (by simp) with h7475 | h7475
                                · linarith only [h4, h7475, hlam]
                                · linarith only [h7338, h7475, hlam]
                              · linarith only [h3, h7474, hlam]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h2, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h7337, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h7339, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h3, h4, h7337, h7348, h7349, h7351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h3, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h7338, hlam, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h7340, hlam, p7455_0]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [h7341, hlam, p7455_1]
                            · have p7455_0 := h7455c.1
                              have p7455_1 := h7455c.2.1
                              have p7455_2 := h7455c.2.2.1
                              have p7455_3 := h7455c.2.2.2
                              linarith only [hlam, p7455_0]
                      · linarith only [h4, h7340, h7350, hlam]
                    · linarith only [h4, h7339, h7349, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7491 | h7491
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7492 | h7492
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7493 | h7493
                        · linarith only [h7344, h7348, h7493, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7495 | h7495
                          · linarith only [h7344, h7348, h7491, h7495, hlam]
                          · rcases h0bigk with h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7337, h7341, h7344, h7348, h7491, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h4, h7337, h7341, h7344, h7348, h7491, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7341, h7344, h7348, h7491, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              rcases p7497_3 (m.d 0 1) (by simp) with h7502 | h7502
                              · rcases p7497_3 (m.d 0 2) (by simp) with h7503 | h7503
                                · linarith only [h0, h7503, hlam]
                                · linarith only [h7338, h7503, hlam]
                              · linarith only [h3, h7502, hlam]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h0, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h4, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7341, h7344, h7348, h7491, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h4, h7341, h7344, h7348, h7491, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h1, hlam, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h4, h7337, h7341, h7344, h7348, h7491, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h4, h7341, h7344, h7348, h7491, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              rcases p7497_3 (m.d 0 1) (by simp) with h7516 | h7516
                              · rcases p7497_3 (m.d 0 2) (by simp) with h7517 | h7517
                                · linarith only [h4, h7517, hlam]
                                · linarith only [h7338, h7517, hlam]
                              · linarith only [h3, h7516, hlam]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h2, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7337, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7339, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h4, h7337, h7341, h7344, h7348, h7491, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h3, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7338, hlam, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7340, hlam, p7497_0]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [h7341, hlam, p7497_1]
                            · have p7497_0 := h7497c.1
                              have p7497_1 := h7497c.2.1
                              have p7497_2 := h7497c.2.2.1
                              have p7497_3 := h7497c.2.2.2
                              linarith only [hlam, p7497_0]
                      · linarith only [h4, h7340, h7492, hlam]
                    · linarith only [h4, h7339, h7491, hlam]
                · linarith only [h7342, h7345, h7347, hlam]
              · linarith only [h7342, h7344, h7346, hlam]
            · linarith only [h4, h7338, h7344, h7345, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h4, h7337, h7344, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7537 | h7537
        · linarith only [h0, h4, h7337, h7537, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7539 | h7539
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7540 | h7540
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7541 | h7541
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7542 | h7542
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7543 | h7543
                  · linarith only [h2, h7341, h7543, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7545 | h7545
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7546 | h7546
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7547 | h7547
                        · linarith only [h2, h7341, h7539, h7547, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7549 | h7549
                          · linarith only [h2, h7341, h7539, h7545, h7549, hlam]
                          · rcases h0bigk with h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c | h7551c
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7553 | h7553
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7554 | h7554
                                · linarith only [h0, h7554, hlam]
                                · rcases p7551_3 (m.d 0 3) (by simp) with h7556 | h7556
                                  · linarith only [h1, h7556, hlam]
                                  · linarith only [h4, h7556, hlam]
                              · linarith only [h0, h7553, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7560 | h7560
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7561 | h7561
                                · linarith only [h0, h7561, hlam]
                                · rcases p7551_3 (m.d 0 3) (by simp) with h7563 | h7563
                                  · linarith only [h1, h7563, hlam]
                                  · rcases p7551_3 (m.d 0 4) (by simp) with h7565 | h7565
                                    · linarith only [h2, h7565, hlam]
                                    · rcases p7551_3 (m.d 0 5) (by simp) with h7567 | h7567
                                      · linarith only [h3, h7567, hlam]
                                      · rcases h2bigk with h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c | h7569c
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7551_1, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h4, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h4, h7545, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h4, h7546, hc01, hc35, hlam, hphi, ht0b, ht5b, p7551_1, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h0, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7537, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h0, h4, h7545, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h0, h4, h7546, hc01, hc35, hlam, hphi, ht0b, ht5b, p7551_1, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          rcases p7569_3 (m.d 0 2) (by simp) with h7580 | h7580
                                          · linarith only [h7580, hlam, p7569_0]
                                          · rcases p7569_3 (m.d 1 2) (by simp) with h7582 | h7582
                                            · linarith only [h7537, h7582, hlam]
                                            · rcases p7569_3 (m.d 2 3) (by simp) with h7584 | h7584
                                              · rcases p7569_3 (m.d 2 4) (by simp) with h7585 | h7585
                                                · linarith only [h7545, h7585, hlam]
                                                · rcases p7569_3 (m.d 2 5) (by simp) with h7587 | h7587
                                                  · linarith only [h7546, h7587, hlam]
                                                  · rcases h3bigk with h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7537, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7551_1, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h4, hlam, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7549, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h1, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7537, hlam, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h1, h7549, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h0, h4, h7540, h7545, h7547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7537, h7540, h7545, h7547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      rcases p7589_3 (m.d 0 3) (by simp) with h7603 | h7603
                                                      · linarith only [h4, h7603, hlam]
                                                      · linarith only [h7339, h7603, hlam]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      rcases p7589_3 (m.d 0 3) (by simp) with h7606 | h7606
                                                      · linarith only [h4, h7606, hlam]
                                                      · linarith only [h7340, h7606, hlam]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7339, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7541, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7545, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7549, hlam, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7340, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7542, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7546, hlam, p7589_0]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [h7340, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7589_1]
                                                    · have p7589_0 := h7589c.1
                                                      have p7589_1 := h7589c.2.1
                                                      have p7589_2 := h7589c.2.2.1
                                                      have p7589_3 := h7589c.2.2.2
                                                      linarith only [hlam, p7589_0]
                                              · linarith only [h7584, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          rcases p7569_3 (m.d 0 2) (by simp) with h7620 | h7620
                                          · linarith only [h4, h7620, hlam]
                                          · linarith only [h0, h7620, hlam]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          rcases p7569_3 (m.d 0 2) (by simp) with h7624 | h7624
                                          · linarith only [h4, h7624, hlam]
                                          · linarith only [h7337, h7624, hlam]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          rcases p7569_3 (m.d 0 2) (by simp) with h7627 | h7627
                                          · linarith only [h4, h7627, hlam]
                                          · linarith only [h7338, h7627, hlam]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7337, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7539, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7545, hlam, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7547, hlam, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7338, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7540, hlam, p7569_0]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h7546, hlam, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [h0, h4, h7540, h7545, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7569_1]
                                        · have p7569_0 := h7569c.1
                                          have p7569_1 := h7569c.2.1
                                          have p7569_2 := h7569c.2.2.1
                                          have p7569_3 := h7569c.2.2.2
                                          linarith only [hlam, p7569_0]
                              · linarith only [h1, h7560, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7641 | h7641
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7642 | h7642
                                · linarith only [h0, h7642, hlam]
                                · linarith only [h7337, h7642, hlam]
                              · linarith only [h2, h7641, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7646 | h7646
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7647 | h7647
                                · linarith only [h0, h7647, hlam]
                                · linarith only [h7338, h7647, hlam]
                              · linarith only [h3, h7646, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h0, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h4, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7654 | h7654
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7655 | h7655
                                · rcases p7551_3 (m.d 0 3) (by simp) with h7656 | h7656
                                  · rcases p7551_3 (m.d 0 4) (by simp) with h7657 | h7657
                                    · linarith only [h7337, h7657, hlam]
                                    · rcases p7551_3 (m.d 0 5) (by simp) with h7659 | h7659
                                      · linarith only [h7338, h7659, hlam]
                                      · linarith only [h7341, h7659, hlam]
                                  · linarith only [h7339, h7656, hlam]
                                · linarith only [h7337, h7655, hlam]
                              · linarith only [h2, h7654, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7665 | h7665
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7666 | h7666
                                · rcases p7551_3 (m.d 0 3) (by simp) with h7667 | h7667
                                  · rcases p7551_3 (m.d 0 4) (by simp) with h7668 | h7668
                                    · linarith only [h7337, h7668, hlam]
                                    · rcases p7551_3 (m.d 0 5) (by simp) with h7670 | h7670
                                      · linarith only [h7338, h7670, hlam]
                                      · rcases h2bigk with h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c | h7672c
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h4, hc12, hc23, hlam, hphi, p7672_1]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h4, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          rcases p7672_3 (m.d 0 2) (by simp) with h7676 | h7676
                                          · rcases p7672_3 (m.d 1 2) (by simp) with h7677 | h7677
                                            · linarith only [h0, h7677, hlam]
                                            · linarith only [h7539, h7677, hlam]
                                          · linarith only [h7676, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          rcases p7672_3 (m.d 0 2) (by simp) with h7681 | h7681
                                          · rcases p7672_3 (m.d 1 2) (by simp) with h7682 | h7682
                                            · linarith only [h0, h7682, hlam]
                                            · linarith only [h7540, h7682, hlam]
                                          · linarith only [h7681, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h0, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7537, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          rcases p7672_3 (m.d 0 2) (by simp) with h7689 | h7689
                                          · rcases p7672_3 (m.d 1 2) (by simp) with h7690 | h7690
                                            · rcases p7672_3 (m.d 2 3) (by simp) with h7691 | h7691
                                              · rcases p7672_3 (m.d 2 4) (by simp) with h7692 | h7692
                                                · linarith only [h7692, hlam, p7672_0]
                                                · rcases p7672_3 (m.d 2 5) (by simp) with h7694 | h7694
                                                  · linarith only [h7540, h7694, hlam]
                                                  · linarith only [h7547, h7694, hlam]
                                              · linarith only [h7545, h7691, hlam]
                                            · linarith only [h7690, hlam, p7672_0]
                                          · linarith only [h7337, h7689, hlam]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          rcases p7672_3 (m.d 0 2) (by simp) with h7700 | h7700
                                          · rcases p7672_3 (m.d 1 2) (by simp) with h7701 | h7701
                                            · rcases p7672_3 (m.d 2 3) (by simp) with h7702 | h7702
                                              · rcases p7672_3 (m.d 2 4) (by simp) with h7703 | h7703
                                                · linarith only [h7539, h7703, hlam]
                                                · rcases p7672_3 (m.d 2 5) (by simp) with h7705 | h7705
                                                  · linarith only [h7705, hlam, p7672_0]
                                                  · rcases h3bigk with h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c | h7707c
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7537, hc03, hc25, hlam, hphi, ht0b, ht5b, p7672_1, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h4, hlam, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      rcases p7707_3 (m.d 0 3) (by simp) with h7711 | h7711
                                                      · rcases p7707_3 (m.d 1 3) (by simp) with h7712 | h7712
                                                        · linarith only [h1, h7712, hlam]
                                                        · linarith only [h7541, h7712, hlam]
                                                      · linarith only [h7711, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      rcases p7707_3 (m.d 0 3) (by simp) with h7716 | h7716
                                                      · rcases p7707_3 (m.d 1 3) (by simp) with h7717 | h7717
                                                        · linarith only [h1, h7717, hlam]
                                                        · linarith only [h7542, h7717, hlam]
                                                      · linarith only [h7716, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h1, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7537, hlam, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h1, h7549, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h2, h4, h7341, h7539, h7545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7551_1, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7537, h7545, h7547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7672_1, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      rcases p7707_3 (m.d 0 3) (by simp) with h7729 | h7729
                                                      · linarith only [h4, h7729, hlam]
                                                      · linarith only [h7339, h7729, hlam]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      rcases p7707_3 (m.d 0 3) (by simp) with h7732 | h7732
                                                      · linarith only [h4, h7732, hlam]
                                                      · linarith only [h7340, h7732, hlam]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7339, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7541, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7545, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7549, hlam, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7340, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7542, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7546, hlam, p7707_0]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [h7340, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7707_1]
                                                    · have p7707_0 := h7707c.1
                                                      have p7707_1 := h7707c.2.1
                                                      have p7707_2 := h7707c.2.2.1
                                                      have p7707_3 := h7707c.2.2.2
                                                      linarith only [hlam, p7707_0]
                                              · linarith only [h7546, h7702, hlam]
                                            · linarith only [h7701, hlam, p7672_0]
                                          · linarith only [h7338, h7700, hlam]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h2, h7341, h7539, h7545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7551_1, p7672_1]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          rcases p7672_3 (m.d 0 2) (by simp) with h7749 | h7749
                                          · linarith only [h4, h7749, hlam]
                                          · linarith only [h0, h7749, hlam]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h2, h4, h7341, h7539, hlam, p7551_1, p7672_2]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h3, h4, h7540, hlam, p7551_1, p7672_2]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7337, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7539, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7545, hlam, p7672_1]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7547, hlam, p7672_1]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7338, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7540, hlam, p7672_0]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h7546, hlam, p7672_1]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [h3, h7540, h7545, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7672_1]
                                        · have p7672_0 := h7672c.1
                                          have p7672_1 := h7672c.2.1
                                          have p7672_2 := h7672c.2.2.1
                                          have p7672_3 := h7672c.2.2.2
                                          linarith only [hlam, p7672_0]
                                  · linarith only [h7340, h7667, hlam]
                                · linarith only [h7338, h7666, hlam]
                              · linarith only [h3, h7665, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h1, hlam, p7551_1]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7769 | h7769
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7770 | h7770
                                · linarith only [h4, h7770, hlam]
                                · rcases p7551_3 (m.d 0 3) (by simp) with h7772 | h7772
                                  · rcases p7551_3 (m.d 0 4) (by simp) with h7773 | h7773
                                    · linarith only [h7339, h7773, hlam]
                                    · rcases p7551_3 (m.d 0 5) (by simp) with h7775 | h7775
                                      · linarith only [h7340, h7775, hlam]
                                      · rcases h2bigk with h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c | h7777c
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h4, hc12, hc23, hlam, hphi, p7551_1, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h4, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h4, h7545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7551_1, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h4, h7546, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7551_1, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h0, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7537, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h0, h4, h7545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7551_1, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h0, h4, h7546, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7551_1, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          rcases p7777_3 (m.d 0 2) (by simp) with h7788 | h7788
                                          · linarith only [h7788, hlam, p7777_0]
                                          · rcases p7777_3 (m.d 1 2) (by simp) with h7790 | h7790
                                            · linarith only [h7537, h7790, hlam]
                                            · rcases p7777_3 (m.d 2 3) (by simp) with h7792 | h7792
                                              · rcases p7777_3 (m.d 2 4) (by simp) with h7793 | h7793
                                                · linarith only [h7545, h7793, hlam]
                                                · rcases p7777_3 (m.d 2 5) (by simp) with h7795 | h7795
                                                  · linarith only [h7546, h7795, hlam]
                                                  · rcases h3bigk with h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c | h7797c
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h4, h7537, hc12, hc23, hlam, hphi, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h4, hlam, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      rcases p7797_3 (m.d 0 3) (by simp) with h7801 | h7801
                                                      · rcases p7797_3 (m.d 1 3) (by simp) with h7802 | h7802
                                                        · linarith only [h1, h7802, hlam]
                                                        · linarith only [h7541, h7802, hlam]
                                                      · linarith only [h7801, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      rcases p7797_3 (m.d 0 3) (by simp) with h7806 | h7806
                                                      · rcases p7797_3 (m.d 1 3) (by simp) with h7807 | h7807
                                                        · linarith only [h1, h7807, hlam]
                                                        · linarith only [h7542, h7807, hlam]
                                                      · linarith only [h7806, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h1, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7537, hlam, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h1, h7549, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [hc02, hc23, hlam, hphi, p7551_1, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7537, h7540, h7545, h7547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      rcases p7797_3 (m.d 0 3) (by simp) with h7819 | h7819
                                                      · linarith only [h4, h7819, hlam]
                                                      · linarith only [h7339, h7819, hlam]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      rcases p7797_3 (m.d 0 3) (by simp) with h7822 | h7822
                                                      · linarith only [h4, h7822, hlam]
                                                      · linarith only [h7340, h7822, hlam]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7339, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7541, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7545, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7549, hlam, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7340, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7542, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7546, hlam, p7797_0]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [h7340, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7797_1]
                                                    · have p7797_0 := h7797c.1
                                                      have p7797_1 := h7797c.2.1
                                                      have p7797_2 := h7797c.2.2.1
                                                      have p7797_3 := h7797c.2.2.2
                                                      linarith only [hlam, p7797_0]
                                              · linarith only [h7792, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          rcases p7777_3 (m.d 0 2) (by simp) with h7836 | h7836
                                          · linarith only [h4, h7836, hlam]
                                          · linarith only [h0, h7836, hlam]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h0, h4, h7540, h7547, hlam, p7551_1, p7777_2]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h0, h4, h7540, hlam, p7551_1, p7777_2]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7337, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7539, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7545, hlam, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7547, hlam, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7338, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7540, hlam, p7777_0]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h7546, hlam, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [h0, h7540, h7545, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7551_1, p7777_1]
                                        · have p7777_0 := h7777c.1
                                          have p7777_1 := h7777c.2.1
                                          have p7777_2 := h7777c.2.2.1
                                          have p7777_3 := h7777c.2.2.2
                                          linarith only [hlam, p7777_0]
                                  · linarith only [h4, h7772, hlam]
                              · linarith only [h0, h7769, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7855 | h7855
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7856 | h7856
                                · linarith only [h4, h7856, hlam]
                                · linarith only [h7337, h7856, hlam]
                              · linarith only [h2, h7855, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7860 | h7860
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7861 | h7861
                                · linarith only [h4, h7861, hlam]
                                · linarith only [h7338, h7861, hlam]
                              · linarith only [h3, h7860, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h2, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h7337, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h7339, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h7341, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h3, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h7338, hlam, p7551_1]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [h7340, hlam, p7551_0]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              rcases p7551_3 (m.d 0 1) (by simp) with h7873 | h7873
                              · rcases p7551_3 (m.d 0 2) (by simp) with h7874 | h7874
                                · rcases p7551_3 (m.d 0 3) (by simp) with h7875 | h7875
                                  · rcases p7551_3 (m.d 0 4) (by simp) with h7876 | h7876
                                    · linarith only [h7341, h7876, hlam]
                                    · rcases p7551_3 (m.d 0 5) (by simp) with h7878 | h7878
                                      · rcases h2bigk with h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c | h7879c
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h4, hc12, hc23, hlam, hphi, p7879_1]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h4, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          rcases p7879_3 (m.d 0 2) (by simp) with h7883 | h7883
                                          · rcases p7879_3 (m.d 1 2) (by simp) with h7884 | h7884
                                            · linarith only [h0, h7884, hlam]
                                            · linarith only [h7539, h7884, hlam]
                                          · linarith only [h7883, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          rcases p7879_3 (m.d 0 2) (by simp) with h7888 | h7888
                                          · rcases p7879_3 (m.d 1 2) (by simp) with h7889 | h7889
                                            · linarith only [h0, h7889, hlam]
                                            · linarith only [h7540, h7889, hlam]
                                          · linarith only [h7888, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h0, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7537, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          rcases p7879_3 (m.d 0 2) (by simp) with h7896 | h7896
                                          · rcases p7879_3 (m.d 1 2) (by simp) with h7897 | h7897
                                            · rcases p7879_3 (m.d 2 3) (by simp) with h7898 | h7898
                                              · rcases p7879_3 (m.d 2 4) (by simp) with h7899 | h7899
                                                · linarith only [h7899, hlam, p7879_0]
                                                · rcases p7879_3 (m.d 2 5) (by simp) with h7901 | h7901
                                                  · linarith only [h7540, h7901, hlam]
                                                  · linarith only [h7547, h7901, hlam]
                                              · linarith only [h7545, h7898, hlam]
                                            · linarith only [h7897, hlam, p7879_0]
                                          · linarith only [h7337, h7896, hlam]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          rcases p7879_3 (m.d 0 2) (by simp) with h7907 | h7907
                                          · rcases p7879_3 (m.d 1 2) (by simp) with h7908 | h7908
                                            · rcases p7879_3 (m.d 2 3) (by simp) with h7909 | h7909
                                              · rcases p7879_3 (m.d 2 4) (by simp) with h7910 | h7910
                                                · linarith only [h7539, h7910, hlam]
                                                · rcases p7879_3 (m.d 2 5) (by simp) with h7912 | h7912
                                                  · linarith only [h7912, hlam, p7879_0]
                                                  · rcases h3bigk with h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c | h7914c
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h4, h7537, h7545, h7547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7879_1, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h4, hlam, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      rcases p7914_3 (m.d 0 3) (by simp) with h7918 | h7918
                                                      · rcases p7914_3 (m.d 1 3) (by simp) with h7919 | h7919
                                                        · linarith only [h1, h7919, hlam]
                                                        · linarith only [h7541, h7919, hlam]
                                                      · linarith only [h7918, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      rcases p7914_3 (m.d 0 3) (by simp) with h7923 | h7923
                                                      · rcases p7914_3 (m.d 1 3) (by simp) with h7924 | h7924
                                                        · linarith only [h1, h7924, hlam]
                                                        · linarith only [h7542, h7924, hlam]
                                                      · linarith only [h7923, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h1, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7537, hlam, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h1, h7549, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h4, hc02, hc23, hlam, hphi, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7537, h7545, h7547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7879_1, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      rcases p7914_3 (m.d 0 3) (by simp) with h7936 | h7936
                                                      · linarith only [h4, h7936, hlam]
                                                      · linarith only [h7339, h7936, hlam]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      rcases p7914_3 (m.d 0 3) (by simp) with h7939 | h7939
                                                      · linarith only [h4, h7939, hlam]
                                                      · linarith only [h7340, h7939, hlam]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7339, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7541, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7545, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7549, hlam, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7340, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7542, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7546, hlam, p7914_0]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [h7340, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7914_1]
                                                    · have p7914_0 := h7914c.1
                                                      have p7914_1 := h7914c.2.1
                                                      have p7914_2 := h7914c.2.2.1
                                                      have p7914_3 := h7914c.2.2.2
                                                      linarith only [hlam, p7914_0]
                                              · linarith only [h7546, h7909, hlam]
                                            · linarith only [h7908, hlam, p7879_0]
                                          · linarith only [h7338, h7907, hlam]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h2, h7338, h7539, h7545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7551_1, p7879_1]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          rcases p7879_3 (m.d 0 2) (by simp) with h7956 | h7956
                                          · linarith only [h4, h7956, hlam]
                                          · linarith only [h0, h7956, hlam]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h2, h4, h7338, h7539, hlam, p7551_1, p7879_2]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          rcases p7879_3 (m.d 0 2) (by simp) with h7961 | h7961
                                          · linarith only [h4, h7961, hlam]
                                          · linarith only [h7338, h7961, hlam]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7337, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7539, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7545, hlam, p7879_1]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7547, hlam, p7879_1]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7338, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7540, hlam, p7879_0]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h7546, hlam, p7879_1]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [h0, h7540, h7545, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7879_1]
                                        · have p7879_0 := h7879c.1
                                          have p7879_1 := h7879c.2.1
                                          have p7879_2 := h7879c.2.2.1
                                          have p7879_3 := h7879c.2.2.2
                                          linarith only [hlam, p7879_0]
                                      · linarith only [h7341, h7878, hlam]
                                  · linarith only [h7339, h7875, hlam]
                                · linarith only [h7337, h7874, hlam]
                              · linarith only [h2, h7873, hlam]
                            · have p7551_0 := h7551c.1
                              have p7551_1 := h7551c.2.1
                              have p7551_2 := h7551c.2.2.1
                              have p7551_3 := h7551c.2.2.2
                              linarith only [hlam, p7551_0]
                      · linarith only [h4, h7340, h7546, hlam]
                    · linarith only [h4, h7339, h7545, hlam]
                · linarith only [h7537, h7540, h7542, hlam]
              · linarith only [h7339, h7341, h7537, h7539, h7541, hc24, hc45, hlam, hphi]
            · linarith only [h4, h7338, h7539, h7540, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h4, h7337, h7539, hc12, hc23, hlam, hphi]
    · linarith only [h4, h7338, h7340, hlam]
  · linarith only [h4, h7337, h7339, hlam]

end R2N4
