import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S40

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10976000 in
set_option maxHeartbeats 10976000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s24 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  rcases m.htr 0 3 5 (by decide) (by decide) with h22354 | h22354
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354
  · rcases m.htr 0 4 5 (by decide) (by decide) with h27342 | h27342
    · linarith only [h22353, h22354, h27342, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h27344 | h27344
      · rcases m.htr 1 2 4 (by decide) (by decide) with h27345 | h27345
        · rcases m.htr 1 2 5 (by decide) (by decide) with h27346 | h27346
          · rcases m.htr 1 3 4 (by decide) (by decide) with h27347 | h27347
            · rcases m.htr 1 3 5 (by decide) (by decide) with h27348 | h27348
              · rcases m.htr 1 4 5 (by decide) (by decide) with h27349 | h27349
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27350 | h27350
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27351 | h27351
                    · linarith only [h22350, h22354, h27351, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27353 | h27353
                      · linarith only [h22351, h27342, h27353, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27355 | h27355
                        · linarith only [h22352, h27342, h27350, h27351, h27355, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h0, hlam, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h15532, hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h18443, hlam, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h20697, hlam, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            rcases p27357_3 (m.d 0 1) (by simp) with h27363 | h27363
                            · linarith only [h0, h27363, hlam]
                            · rcases p27357_3 (m.d 0 2) (by simp) with h27365 | h27365
                              · rcases p27357_3 (m.d 0 3) (by simp) with h27366 | h27366
                                · linarith only [h22350, h27366, hlam]
                                · linarith only [h15532, h27366, hlam]
                              · linarith only [h0, h27365, hlam]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            rcases p27357_3 (m.d 0 1) (by simp) with h27371 | h27371
                            · linarith only [h0, h27371, hlam]
                            · rcases p27357_3 (m.d 0 2) (by simp) with h27373 | h27373
                              · rcases p27357_3 (m.d 0 3) (by simp) with h27374 | h27374
                                · linarith only [h22350, h27374, hlam]
                                · rcases p27357_3 (m.d 0 4) (by simp) with h27376 | h27376
                                  · linarith only [h22351, h27376, hlam]
                                  · rcases p27357_3 (m.d 0 5) (by simp) with h27378 | h27378
                                    · linarith only [h22352, h27378, hlam]
                                    · linarith only [h22354, h27378, hlam]
                              · linarith only [h22350, h27373, hlam]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            rcases p27357_3 (m.d 0 1) (by simp) with h27382 | h27382
                            · linarith only [h0, h27382, hlam]
                            · rcases p27357_3 (m.d 0 2) (by simp) with h27384 | h27384
                              · rcases p27357_3 (m.d 0 3) (by simp) with h27385 | h27385
                                · linarith only [h22350, h27385, hlam]
                                · linarith only [h22353, h27385, hlam]
                              · linarith only [h22351, h27384, hlam]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            rcases p27357_3 (m.d 0 1) (by simp) with h27389 | h27389
                            · linarith only [h0, h27389, hlam]
                            · rcases p27357_3 (m.d 0 2) (by simp) with h27391 | h27391
                              · rcases p27357_3 (m.d 0 3) (by simp) with h27392 | h27392
                                · linarith only [h22350, h27392, hlam]
                                · rcases p27357_3 (m.d 0 4) (by simp) with h27394 | h27394
                                  · linarith only [h22351, h27394, hlam]
                                  · rcases p27357_3 (m.d 0 5) (by simp) with h27396 | h27396
                                    · linarith only [h22352, h27396, hlam]
                                    · rcases h2bigk with h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c | h27398c
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h0, hlam, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        rcases p27398_3 (m.d 0 2) (by simp) with h27401 | h27401
                                        · rcases p27398_3 (m.d 1 2) (by simp) with h27402 | h27402
                                          · rcases p27398_3 (m.d 2 3) (by simp) with h27403 | h27403
                                            · linarith only [h27403, hlam, p27398_0]
                                            · rcases p27398_3 (m.d 2 4) (by simp) with h27405 | h27405
                                              · linarith only [h22351, h27405, hlam]
                                              · rcases p27398_3 (m.d 2 5) (by simp) with h27407 | h27407
                                                · linarith only [h22352, h27407, hlam]
                                                · linarith only [h27351, h27407, hlam]
                                          · linarith only [h27344, h27402, hlam]
                                        · linarith only [h27401, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        rcases p27398_3 (m.d 0 2) (by simp) with h27412 | h27412
                                        · rcases p27398_3 (m.d 1 2) (by simp) with h27413 | h27413
                                          · rcases p27398_3 (m.d 2 3) (by simp) with h27414 | h27414
                                            · linarith only [h22350, h27414, hlam]
                                            · linarith only [h27350, h27414, hlam]
                                          · linarith only [h27345, h27413, hlam]
                                        · linarith only [h27412, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        rcases p27398_3 (m.d 0 2) (by simp) with h27419 | h27419
                                        · rcases p27398_3 (m.d 1 2) (by simp) with h27420 | h27420
                                          · rcases p27398_3 (m.d 2 3) (by simp) with h27421 | h27421
                                            · linarith only [h22350, h27421, hlam]
                                            · rcases p27398_3 (m.d 2 4) (by simp) with h27423 | h27423
                                              · linarith only [h22351, h27423, hlam]
                                              · rcases p27398_3 (m.d 2 5) (by simp) with h27425 | h27425
                                                · linarith only [h27425, hlam, p27398_0]
                                                · rcases h3bigk with h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c | h27427c
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h15532, hlam, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22354, h27344, h27347, h27349, h27355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22354, h27344, h27347, h27349, h27355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22354, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    rcases p27427_3 (m.d 0 3) (by simp) with h27433 | h27433
                                                    · linarith only [h15532, h27433, hlam]
                                                    · rcases p27427_3 (m.d 1 3) (by simp) with h27435 | h27435
                                                      · rcases p27427_3 (m.d 2 3) (by simp) with h27436 | h27436
                                                        · linarith only [h27344, h27436, hlam]
                                                        · rcases p27427_3 (m.d 3 4) (by simp) with h27438 | h27438
                                                          · linarith only [h27347, h27438, hlam]
                                                          · rcases p27427_3 (m.d 3 5) (by simp) with h27440 | h27440
                                                            · linarith only [h27348, h27440, hlam]
                                                            · linarith only [h22354, h27440, hlam]
                                                      · linarith only [h15532, h27435, hlam]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    rcases p27427_3 (m.d 0 3) (by simp) with h27445 | h27445
                                                    · linarith only [h15532, h27445, hlam]
                                                    · linarith only [h22350, h27445, hlam]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22350, h22354, h27347, h27349, h27350, h27355, hlam, p27427_2]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22350, h22354, h27344, h27350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22350, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27344, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h0, h22350, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27357_1, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27351, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h22353, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27347, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27350, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27355, hlam, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h15532, h27344, h27348, hc01, hc12, hlam, hphi, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27348, hlam, p27427_0]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [h27344, h27348, h27350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27427_1]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    rcases p27427_3 (m.d 0 3) (by simp) with h27463 | h27463
                                                    · linarith only [h22354, h27463, hlam]
                                                    · linarith only [h22353, h27463, hlam]
                                                  · have p27427_0 := h27427c.1
                                                    have p27427_1 := h27427c.2.1
                                                    have p27427_2 := h27427c.2.2.1
                                                    have p27427_3 := h27427c.2.2.2
                                                    linarith only [hlam, p27427_0]
                                          · linarith only [h27346, h27420, hlam]
                                        · linarith only [h27419, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p27357_1, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        rcases p27398_3 (m.d 0 2) (by simp) with h27471 | h27471
                                        · linarith only [h0, h27471, hlam]
                                        · linarith only [h22350, h27471, hlam]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        rcases p27398_3 (m.d 0 2) (by simp) with h27474 | h27474
                                        · linarith only [h0, h27474, hlam]
                                        · linarith only [h22351, h27474, hlam]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        rcases p27398_3 (m.d 0 2) (by simp) with h27477 | h27477
                                        · linarith only [h0, h27477, hlam]
                                        · linarith only [h22352, h27477, hlam]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h22350, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h27344, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h22350, h22354, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p27357_1, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h27351, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h22351, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h27345, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h27350, hlam, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h27353, hlam, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h22352, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h27346, hlam, p27398_0]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h0, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27357_1, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [h0, h22352, h27350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27357_1, p27398_1]
                                      · have p27398_0 := h27398c.1
                                        have p27398_1 := h27398c.2.1
                                        have p27398_2 := h27398c.2.2.1
                                        have p27398_3 := h27398c.2.2.2
                                        linarith only [hlam, p27398_0]
                              · linarith only [h22352, h27391, hlam]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22354, h27344, h27347, h27349, h27355, hc01, hc12, hlam, hphi, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22350, hlam, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h18443, h22354, h27344, h27347, h27349, h27355, hc01, hc12, hlam, hphi, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22354, hlam, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22353, h22354, h27344, h27347, h27349, h27355, hc01, hc12, hlam, hphi, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22351, hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22353, hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h27342, hlam, p27357_0]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22354, h27344, h27347, h27349, h27355, hc01, hc12, hlam, hphi, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h22352, hlam, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h15532, h22354, h27344, h27347, h27349, h27355, hc01, hc12, hlam, hphi, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [h18443, h22354, h27344, h27347, h27349, h27355, hc01, hc12, hlam, hphi, p27357_1]
                          · have p27357_0 := h27357c.1
                            have p27357_1 := h27357c.2.1
                            have p27357_2 := h27357c.2.2.1
                            have p27357_3 := h27357c.2.2.2
                            linarith only [hlam, p27357_0]
                  · linarith only [h22353, h22354, h27350, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27512 | h27512
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27513 | h27513
                    · linarith only [h0, h15532, h22350, h22354, h27513, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27515 | h27515
                      · linarith only [h18443, h27349, h27515, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27517 | h27517
                        · linarith only [h18443, h22350, h27349, h27512, h27517, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c | h27519c
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h0, hlam, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h15532, hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h18443, hlam, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h20697, hlam, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            rcases p27519_3 (m.d 0 1) (by simp) with h27525 | h27525
                            · linarith only [h0, h27525, hlam]
                            · rcases p27519_3 (m.d 0 2) (by simp) with h27527 | h27527
                              · rcases p27519_3 (m.d 0 3) (by simp) with h27528 | h27528
                                · linarith only [h22350, h27528, hlam]
                                · linarith only [h15532, h27528, hlam]
                              · linarith only [h0, h27527, hlam]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            rcases p27519_3 (m.d 0 1) (by simp) with h27533 | h27533
                            · linarith only [h0, h27533, hlam]
                            · rcases p27519_3 (m.d 0 2) (by simp) with h27535 | h27535
                              · rcases p27519_3 (m.d 0 3) (by simp) with h27536 | h27536
                                · linarith only [h22350, h27536, hlam]
                                · rcases p27519_3 (m.d 0 4) (by simp) with h27538 | h27538
                                  · linarith only [h22351, h27538, hlam]
                                  · rcases p27519_3 (m.d 0 5) (by simp) with h27540 | h27540
                                    · linarith only [h22352, h27540, hlam]
                                    · linarith only [h22354, h27540, hlam]
                              · linarith only [h22350, h27535, hlam]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            rcases p27519_3 (m.d 0 1) (by simp) with h27544 | h27544
                            · linarith only [h0, h27544, hlam]
                            · rcases p27519_3 (m.d 0 2) (by simp) with h27546 | h27546
                              · rcases p27519_3 (m.d 0 3) (by simp) with h27547 | h27547
                                · linarith only [h22350, h27547, hlam]
                                · linarith only [h22353, h27547, hlam]
                              · linarith only [h22351, h27546, hlam]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            rcases p27519_3 (m.d 0 1) (by simp) with h27551 | h27551
                            · linarith only [h0, h27551, hlam]
                            · rcases p27519_3 (m.d 0 2) (by simp) with h27553 | h27553
                              · rcases p27519_3 (m.d 0 3) (by simp) with h27554 | h27554
                                · linarith only [h22350, h27554, hlam]
                                · rcases p27519_3 (m.d 0 4) (by simp) with h27556 | h27556
                                  · linarith only [h22351, h27556, hlam]
                                  · rcases p27519_3 (m.d 0 5) (by simp) with h27558 | h27558
                                    · linarith only [h22352, h27558, hlam]
                                    · rcases h2bigk with h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c | h27560c
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h0, hlam, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        rcases p27560_3 (m.d 0 2) (by simp) with h27563 | h27563
                                        · rcases p27560_3 (m.d 1 2) (by simp) with h27564 | h27564
                                          · rcases p27560_3 (m.d 2 3) (by simp) with h27565 | h27565
                                            · linarith only [h27565, hlam, p27560_0]
                                            · rcases p27560_3 (m.d 2 4) (by simp) with h27567 | h27567
                                              · linarith only [h22351, h27567, hlam]
                                              · rcases p27560_3 (m.d 2 5) (by simp) with h27569 | h27569
                                                · linarith only [h22352, h27569, hlam]
                                                · linarith only [h27513, h27569, hlam]
                                          · linarith only [h27344, h27564, hlam]
                                        · linarith only [h27563, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        rcases p27560_3 (m.d 0 2) (by simp) with h27574 | h27574
                                        · rcases p27560_3 (m.d 1 2) (by simp) with h27575 | h27575
                                          · rcases p27560_3 (m.d 2 3) (by simp) with h27576 | h27576
                                            · linarith only [h22350, h27576, hlam]
                                            · linarith only [h27512, h27576, hlam]
                                          · linarith only [h27345, h27575, hlam]
                                        · linarith only [h27574, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        rcases p27560_3 (m.d 0 2) (by simp) with h27581 | h27581
                                        · rcases p27560_3 (m.d 1 2) (by simp) with h27582 | h27582
                                          · rcases p27560_3 (m.d 2 3) (by simp) with h27583 | h27583
                                            · linarith only [h22350, h27583, hlam]
                                            · rcases p27560_3 (m.d 2 4) (by simp) with h27585 | h27585
                                              · linarith only [h22351, h27585, hlam]
                                              · rcases p27560_3 (m.d 2 5) (by simp) with h27587 | h27587
                                                · linarith only [h27587, hlam, p27560_0]
                                                · rcases h3bigk with h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c | h27589c
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h15532, hlam, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h0, h22354, h27512, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27519_1, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h0, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27519_1, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h22354, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    rcases p27589_3 (m.d 0 3) (by simp) with h27595 | h27595
                                                    · linarith only [h15532, h27595, hlam]
                                                    · rcases p27589_3 (m.d 1 3) (by simp) with h27597 | h27597
                                                      · rcases p27589_3 (m.d 2 3) (by simp) with h27598 | h27598
                                                        · linarith only [h27344, h27598, hlam]
                                                        · rcases p27589_3 (m.d 3 4) (by simp) with h27600 | h27600
                                                          · linarith only [h27347, h27600, hlam]
                                                          · rcases p27589_3 (m.d 3 5) (by simp) with h27602 | h27602
                                                            · linarith only [h27348, h27602, hlam]
                                                            · linarith only [h22354, h27602, hlam]
                                                      · linarith only [h15532, h27597, hlam]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    rcases p27589_3 (m.d 0 3) (by simp) with h27607 | h27607
                                                    · linarith only [h15532, h27607, hlam]
                                                    · linarith only [h22350, h27607, hlam]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h22350, h22354, h27348, h27512, hlam, p27589_2]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h15532, h22354, hc01, hc13, hlam, hphi, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h22350, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27344, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h0, h22350, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27519_1, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27513, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h22353, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27347, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27512, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27517, hlam, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h15532, h27344, h27348, hc01, hc12, hlam, hphi, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27348, hlam, p27589_0]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [h27344, h27348, h27512, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27589_1]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    rcases p27589_3 (m.d 0 3) (by simp) with h27625 | h27625
                                                    · linarith only [h22354, h27625, hlam]
                                                    · linarith only [h22353, h27625, hlam]
                                                  · have p27589_0 := h27589c.1
                                                    have p27589_1 := h27589c.2.1
                                                    have p27589_2 := h27589c.2.2.1
                                                    have p27589_3 := h27589c.2.2.2
                                                    linarith only [hlam, p27589_0]
                                          · linarith only [h27346, h27582, hlam]
                                        · linarith only [h27581, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p27519_1, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        rcases p27560_3 (m.d 0 2) (by simp) with h27633 | h27633
                                        · linarith only [h0, h27633, hlam]
                                        · linarith only [h22350, h27633, hlam]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        rcases p27560_3 (m.d 0 2) (by simp) with h27636 | h27636
                                        · linarith only [h0, h27636, hlam]
                                        · linarith only [h22351, h27636, hlam]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        rcases p27560_3 (m.d 0 2) (by simp) with h27639 | h27639
                                        · linarith only [h0, h27639, hlam]
                                        · linarith only [h22352, h27639, hlam]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h22350, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h27344, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h22350, h22354, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p27519_1, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h27513, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h22351, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h27345, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h27512, hlam, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h27515, hlam, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h22352, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h27346, hlam, p27560_0]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h0, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27519_1, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [h0, h22352, h27512, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27519_1, p27560_1]
                                      · have p27560_0 := h27560c.1
                                        have p27560_1 := h27560c.2.1
                                        have p27560_2 := h27560c.2.2.1
                                        have p27560_3 := h27560c.2.2.2
                                        linarith only [hlam, p27560_0]
                              · linarith only [h22352, h27553, hlam]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22354, h27344, h27348, hc01, hc12, hlam, hphi, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22350, hlam, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h18443, h22354, h27344, h27348, hc01, hc12, hlam, hphi, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22354, hlam, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22353, h22354, h27344, h27348, hc01, hc12, hlam, hphi, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22351, hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22353, hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h27342, hlam, p27519_0]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22354, h27344, h27348, hc01, hc12, hlam, hphi, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h22352, hlam, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h15532, h22354, h27344, h27348, hc01, hc12, hlam, hphi, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [h18443, h22354, h27344, h27348, hc01, hc12, hlam, hphi, p27519_1]
                          · have p27519_0 := h27519c.1
                            have p27519_1 := h27519c.2.1
                            have p27519_2 := h27519c.2.2.1
                            have p27519_3 := h27519c.2.2.2
                            linarith only [hlam, p27519_0]
                  · linarith only [h22353, h22354, h27344, h27348, h27512, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h27674 | h27674
                · linarith only [h18443, h27342, h27347, h27348, h27674, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27676 | h27676
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27677 | h27677
                    · linarith only [h15532, h27348, h27677, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27679 | h27679
                      · linarith only [h18443, h27674, h27679, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27681 | h27681
                        · linarith only [h18443, h27674, h27681, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c | h27683c
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h0, hlam, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h15532, hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h18443, hlam, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h20697, hlam, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            rcases p27683_3 (m.d 0 1) (by simp) with h27689 | h27689
                            · linarith only [h0, h27689, hlam]
                            · rcases p27683_3 (m.d 0 2) (by simp) with h27691 | h27691
                              · rcases p27683_3 (m.d 0 3) (by simp) with h27692 | h27692
                                · linarith only [h22350, h27692, hlam]
                                · linarith only [h15532, h27692, hlam]
                              · linarith only [h0, h27691, hlam]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            rcases p27683_3 (m.d 0 1) (by simp) with h27697 | h27697
                            · linarith only [h0, h27697, hlam]
                            · rcases p27683_3 (m.d 0 2) (by simp) with h27699 | h27699
                              · rcases p27683_3 (m.d 0 3) (by simp) with h27700 | h27700
                                · linarith only [h22350, h27700, hlam]
                                · rcases p27683_3 (m.d 0 4) (by simp) with h27702 | h27702
                                  · linarith only [h22351, h27702, hlam]
                                  · rcases p27683_3 (m.d 0 5) (by simp) with h27704 | h27704
                                    · linarith only [h22352, h27704, hlam]
                                    · linarith only [h22354, h27704, hlam]
                              · linarith only [h22350, h27699, hlam]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            rcases p27683_3 (m.d 0 1) (by simp) with h27708 | h27708
                            · linarith only [h0, h27708, hlam]
                            · rcases p27683_3 (m.d 0 2) (by simp) with h27710 | h27710
                              · rcases p27683_3 (m.d 0 3) (by simp) with h27711 | h27711
                                · linarith only [h22350, h27711, hlam]
                                · linarith only [h22353, h27711, hlam]
                              · linarith only [h22351, h27710, hlam]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            rcases p27683_3 (m.d 0 1) (by simp) with h27715 | h27715
                            · linarith only [h0, h27715, hlam]
                            · rcases p27683_3 (m.d 0 2) (by simp) with h27717 | h27717
                              · rcases p27683_3 (m.d 0 3) (by simp) with h27718 | h27718
                                · linarith only [h22350, h27718, hlam]
                                · rcases p27683_3 (m.d 0 4) (by simp) with h27720 | h27720
                                  · linarith only [h22351, h27720, hlam]
                                  · rcases p27683_3 (m.d 0 5) (by simp) with h27722 | h27722
                                    · linarith only [h22352, h27722, hlam]
                                    · rcases h2bigk with h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c | h27724c
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h0, hlam, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        rcases p27724_3 (m.d 0 2) (by simp) with h27727 | h27727
                                        · rcases p27724_3 (m.d 1 2) (by simp) with h27728 | h27728
                                          · rcases p27724_3 (m.d 2 3) (by simp) with h27729 | h27729
                                            · linarith only [h27729, hlam, p27724_0]
                                            · rcases p27724_3 (m.d 2 4) (by simp) with h27731 | h27731
                                              · linarith only [h22351, h27731, hlam]
                                              · rcases p27724_3 (m.d 2 5) (by simp) with h27733 | h27733
                                                · linarith only [h22352, h27733, hlam]
                                                · linarith only [h27677, h27733, hlam]
                                          · linarith only [h27344, h27728, hlam]
                                        · linarith only [h27727, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        rcases p27724_3 (m.d 0 2) (by simp) with h27738 | h27738
                                        · rcases p27724_3 (m.d 1 2) (by simp) with h27739 | h27739
                                          · rcases p27724_3 (m.d 2 3) (by simp) with h27740 | h27740
                                            · linarith only [h22350, h27740, hlam]
                                            · linarith only [h27676, h27740, hlam]
                                          · linarith only [h27345, h27739, hlam]
                                        · linarith only [h27738, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        rcases p27724_3 (m.d 0 2) (by simp) with h27745 | h27745
                                        · rcases p27724_3 (m.d 1 2) (by simp) with h27746 | h27746
                                          · rcases p27724_3 (m.d 2 3) (by simp) with h27747 | h27747
                                            · linarith only [h22350, h27747, hlam]
                                            · rcases p27724_3 (m.d 2 4) (by simp) with h27749 | h27749
                                              · linarith only [h22351, h27749, hlam]
                                              · rcases p27724_3 (m.d 2 5) (by simp) with h27751 | h27751
                                                · linarith only [h27751, hlam, p27724_0]
                                                · rcases h3bigk with h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c | h27753c
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h15532, hlam, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h0, h22354, h27676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27683_1, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h0, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27683_1, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h22354, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h22350, h27348, h27676, h27681, hc34, hc45, hlam, hphi, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27348, h27676, h27681, hc34, hc45, hlam, hphi, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27348, h27681, hc34, hc45, hlam, hphi, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27348, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h22350, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27344, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h15532, h22350, h27348, h27681, hc34, hc45, hlam, hphi, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27677, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h22353, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27347, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27676, hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [hlam, p27753_0]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27681, hlam, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h22353, h27681, hc34, hc45, hlam, hphi, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h15532, h27681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [h27676, h27681, hc34, hc45, hlam, hphi, p27753_1]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    rcases p27753_3 (m.d 0 3) (by simp) with h27777 | h27777
                                                    · linarith only [h22354, h27777, hlam]
                                                    · linarith only [h22353, h27777, hlam]
                                                  · have p27753_0 := h27753c.1
                                                    have p27753_1 := h27753c.2.1
                                                    have p27753_2 := h27753c.2.2.1
                                                    have p27753_3 := h27753c.2.2.2
                                                    linarith only [hlam, p27753_0]
                                          · linarith only [h27346, h27746, hlam]
                                        · linarith only [h27745, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h22350, h22354, h27676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27683_1, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        rcases p27724_3 (m.d 0 2) (by simp) with h27785 | h27785
                                        · linarith only [h0, h27785, hlam]
                                        · linarith only [h22350, h27785, hlam]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        rcases p27724_3 (m.d 0 2) (by simp) with h27788 | h27788
                                        · linarith only [h0, h27788, hlam]
                                        · linarith only [h22351, h27788, hlam]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        rcases p27724_3 (m.d 0 2) (by simp) with h27791 | h27791
                                        · linarith only [h0, h27791, hlam]
                                        · linarith only [h22352, h27791, hlam]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h22350, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h27344, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h22350, h22354, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p27683_1, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h27677, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h22351, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h27345, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h27676, hlam, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h27679, hlam, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h22352, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h27346, hlam, p27724_0]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h0, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27683_1, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [h0, h22352, h27676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27683_1, p27724_1]
                                      · have p27724_0 := h27724c.1
                                        have p27724_1 := h27724c.2.1
                                        have p27724_2 := h27724c.2.2.1
                                        have p27724_3 := h27724c.2.2.2
                                        linarith only [hlam, p27724_0]
                              · linarith only [h22352, h27717, hlam]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22354, h27681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22350, hlam, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h18443, h22354, h27681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22354, hlam, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22353, h22354, h27681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22351, hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22353, hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h27342, hlam, p27683_0]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            rcases p27683_3 (m.d 0 1) (by simp) with h27820 | h27820
                            · linarith only [h20697, h27820, hlam]
                            · rcases p27683_3 (m.d 0 2) (by simp) with h27822 | h27822
                              · rcases p27683_3 (m.d 0 3) (by simp) with h27823 | h27823
                                · linarith only [h22354, h27823, hlam]
                                · linarith only [h15532, h27823, hlam]
                              · linarith only [h0, h27822, hlam]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22352, hlam, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [h22350, h22354, h27676, h27681, hc34, hc45, hlam, hphi, p27683_1]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            rcases p27683_3 (m.d 0 1) (by simp) with h27829 | h27829
                            · linarith only [h20697, h27829, hlam]
                            · rcases p27683_3 (m.d 0 2) (by simp) with h27831 | h27831
                              · rcases p27683_3 (m.d 0 3) (by simp) with h27832 | h27832
                                · linarith only [h22354, h27832, hlam]
                                · linarith only [h22353, h27832, hlam]
                              · linarith only [h22351, h27831, hlam]
                          · have p27683_0 := h27683c.1
                            have p27683_1 := h27683c.2.1
                            have p27683_2 := h27683c.2.2.1
                            have p27683_3 := h27683c.2.2.2
                            linarith only [hlam, p27683_0]
                  · linarith only [h22353, h22354, h27676, hc23, hc35, hlam, hphi]
            · linarith only [h15532, h22353, h27347, hlam]
          · linarith only [h0, h22352, h27346, hlam]
        · linarith only [h0, h22351, h27345, hlam]
      · linarith only [h0, h22350, h27344, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s24 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353

end R2N4
