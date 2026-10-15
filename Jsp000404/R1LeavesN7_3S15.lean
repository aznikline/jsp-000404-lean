import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10366 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h10368 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h10370 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 3 5 (by decide) (by decide) with h10371 | h10371
  · rcases m.htr 1 4 5 (by decide) (by decide) with h10372 | h10372
    · rcases m.htr 2 3 4 (by decide) (by decide) with h10373 | h10373
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10374 | h10374
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10375 | h10375
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10376 | h10376
            · rcases h1bigk with h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10379 | h10379
                · rcases p10377_3 (m.d 1 2) (by simp) with h10380 | h10380
                  · linarith only [h10380, hlam, p10377_0]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10382 | h10382
                    · linarith only [h1, h10382, hlam]
                    · linarith only [h10364, h10382, hlam]
                · linarith only [h10379, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10370, h10376, hc01, hc45, hlam, hphi, ht0b, ht5b, p10377_1]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10387 | h10387
                · rcases p10377_3 (m.d 1 2) (by simp) with h10388 | h10388
                  · linarith only [h0, h10388, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10390 | h10390
                    · linarith only [h1, h10390, hlam]
                    · linarith only [h10370, h10390, hlam]
                · linarith only [h10387, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10394 | h10394
                · rcases p10377_3 (m.d 1 2) (by simp) with h10395 | h10395
                  · linarith only [h0, h10395, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10397 | h10397
                    · linarith only [h1, h10397, hlam]
                    · linarith only [h10371, h10397, hlam]
                · linarith only [h10394, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h0, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10364, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10366, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10368, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h1, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10407 | h10407
                · rcases p10377_3 (m.d 1 2) (by simp) with h10408 | h10408
                  · linarith only [h10364, h10408, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10410 | h10410
                    · rcases p10377_3 (m.d 1 4) (by simp) with h10411 | h10411
                      · linarith only [h10370, h10411, hlam]
                      · linarith only [h10366, h10411, hlam]
                    · linarith only [h10364, h10410, hlam]
                · linarith only [h0, h10407, hlam]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h1, h10370, h10376, hc01, hc45, hlam, hphi, ht0b, ht5b, p10377_1]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10418 | h10418
                · rcases p10377_3 (m.d 1 2) (by simp) with h10419 | h10419
                  · linarith only [h10364, h10419, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10421 | h10421
                    · rcases p10377_3 (m.d 1 4) (by simp) with h10422 | h10422
                      · linarith only [h10370, h10422, hlam]
                      · linarith only [h10372, h10422, hlam]
                    · linarith only [h10371, h10421, hlam]
                · linarith only [h10418, h3, hlam]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h2, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10428 | h10428
                · rcases p10377_3 (m.d 1 2) (by simp) with h10429 | h10429
                  · linarith only [h10366, h10429, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10431 | h10431
                    · rcases p10377_3 (m.d 1 4) (by simp) with h10432 | h10432
                      · rcases p10377_3 (m.d 1 5) (by simp) with h10433 | h10433
                        · linarith only [h10372, h10433, hlam]
                        · linarith only [h10368, h10433, hlam]
                      · linarith only [h10366, h10432, hlam]
                    · linarith only [h10364, h10431, hlam]
                · linarith only [h0, h10428, hlam]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10370, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10441 | h10441
                · rcases p10377_3 (m.d 1 2) (by simp) with h10442 | h10442
                  · linarith only [h10366, h10442, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10444 | h10444
                    · rcases p10377_3 (m.d 1 4) (by simp) with h10445 | h10445
                      · rcases p10377_3 (m.d 1 5) (by simp) with h10446 | h10446
                        · linarith only [h10372, h10446, hlam]
                        · rcases h3bigk with h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10368, h10370, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10377_1, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h4, hlam, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 3) (by simp) with h10452 | h10452
                            · rcases p10448_3 (m.d 1 3) (by simp) with h10453 | h10453
                              · linarith only [h1, h10453, hlam]
                              · linarith only [h10370, h10453, hlam]
                            · linarith only [h10452, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 3) (by simp) with h10457 | h10457
                            · rcases p10448_3 (m.d 1 3) (by simp) with h10458 | h10458
                              · linarith only [h1, h10458, hlam]
                              · linarith only [h10371, h10458, hlam]
                            · linarith only [h10457, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h1, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10364, hlam, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h1, h10376, hc01, hc45, hlam, hphi, ht0b, ht5b, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 3) (by simp) with h10466 | h10466
                            · rcases p10448_3 (m.d 1 3) (by simp) with h10467 | h10467
                              · rcases p10448_3 (m.d 2 3) (by simp) with h10468 | h10468
                                · rcases p10448_3 (m.d 3 4) (by simp) with h10469 | h10469
                                  · linarith only [h10370, h10469, hlam]
                                  · linarith only [h10376, h10469, hlam]
                                · linarith only [h10374, h10468, hlam]
                              · linarith only [h10467, hlam, p10448_0]
                            · linarith only [h10362, h10466, hlam]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10361, h10376, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10370, h10376, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 3) (by simp) with h10478 | h10478
                            · linarith only [h10478, h4, hlam]
                            · linarith only [h10361, h10478, hlam]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 3) (by simp) with h10481 | h10481
                            · linarith only [h10481, h4, hlam]
                            · linarith only [h10362, h10481, hlam]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10361, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10370, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10373, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h1, h10370, hc01, hc35, hlam, hphi, ht0b, ht5b, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10362, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10371, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10374, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h10376, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                      · linarith only [h10372, h10445, hlam]
                    · linarith only [h10371, h10444, hlam]
                · linarith only [h10441, h3, hlam]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h3, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                rcases p10377_3 (m.d 0 1) (by simp) with h10498 | h10498
                · rcases p10377_3 (m.d 1 2) (by simp) with h10499 | h10499
                  · linarith only [h10368, h10499, hlam]
                  · rcases p10377_3 (m.d 1 3) (by simp) with h10501 | h10501
                    · rcases p10377_3 (m.d 1 4) (by simp) with h10502 | h10502
                      · rcases p10377_3 (m.d 1 5) (by simp) with h10503 | h10503
                        · rcases h3bigk with h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c | h10504c
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10371, h4, hc12, hc23, hlam, hphi, p10377_1, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h4, hlam, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            rcases p10504_3 (m.d 0 3) (by simp) with h10508 | h10508
                            · rcases p10504_3 (m.d 1 3) (by simp) with h10509 | h10509
                              · linarith only [h1, h10509, hlam]
                              · linarith only [h10370, h10509, hlam]
                            · linarith only [h10508, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            rcases p10504_3 (m.d 0 3) (by simp) with h10513 | h10513
                            · rcases p10504_3 (m.d 1 3) (by simp) with h10514 | h10514
                              · linarith only [h1, h10514, hlam]
                              · linarith only [h10371, h10514, hlam]
                            · linarith only [h10513, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h1, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10364, hlam, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h1, h10376, hc01, hc45, hlam, hphi, ht0b, ht5b, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            rcases p10504_3 (m.d 0 3) (by simp) with h10522 | h10522
                            · rcases p10504_3 (m.d 1 3) (by simp) with h10523 | h10523
                              · rcases p10504_3 (m.d 2 3) (by simp) with h10524 | h10524
                                · rcases p10504_3 (m.d 3 4) (by simp) with h10525 | h10525
                                  · linarith only [h10370, h10525, hlam]
                                  · linarith only [h10376, h10525, hlam]
                                · linarith only [h10374, h10524, hlam]
                              · linarith only [h10523, hlam, p10504_0]
                            · linarith only [h10362, h10522, hlam]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10361, h10376, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10370, h10376, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            rcases p10504_3 (m.d 0 3) (by simp) with h10534 | h10534
                            · linarith only [h10534, h4, hlam]
                            · linarith only [h10361, h10534, hlam]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            rcases p10504_3 (m.d 0 3) (by simp) with h10537 | h10537
                            · linarith only [h10537, h4, hlam]
                            · linarith only [h10362, h10537, hlam]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10361, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10370, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10373, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h1, h10370, hc01, hc35, hlam, hphi, ht0b, ht5b, p10504_1]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10362, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10371, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10374, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [h10376, hlam, p10504_0]
                          · have p10504_0 := h10504c.1
                            have p10504_1 := h10504c.2.1
                            have p10504_2 := h10504c.2.2.1
                            have p10504_3 := h10504c.2.2.2
                            linarith only [hlam, p10504_0]
                        · linarith only [h10368, h10503, hlam]
                      · linarith only [h10366, h10502, hlam]
                    · linarith only [h10364, h10501, hlam]
                · linarith only [h0, h10498, hlam]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10371, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [h10372, hlam, p10377_0]
              · have p10377_0 := h10377c.1
                have p10377_1 := h10377c.2.1
                have p10377_2 := h10377c.2.2.1
                have p10377_3 := h10377c.2.2.2
                linarith only [hlam, p10377_0]
            · rcases h1bigk with h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                rcases p10557_3 (m.d 0 1) (by simp) with h10559 | h10559
                · rcases p10557_3 (m.d 1 2) (by simp) with h10560 | h10560
                  · linarith only [h10560, hlam, p10557_0]
                  · rcases p10557_3 (m.d 1 3) (by simp) with h10562 | h10562
                    · linarith only [h1, h10562, hlam]
                    · linarith only [h10364, h10562, hlam]
                · linarith only [h10559, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10370, h10372, h10376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10372, h10376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                rcases p10557_3 (m.d 0 1) (by simp) with h10568 | h10568
                · rcases p10557_3 (m.d 1 2) (by simp) with h10569 | h10569
                  · linarith only [h0, h10569, hlam]
                  · rcases p10557_3 (m.d 1 3) (by simp) with h10571 | h10571
                    · linarith only [h1, h10571, hlam]
                    · linarith only [h10371, h10571, hlam]
                · linarith only [h10568, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h0, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10364, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10366, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10368, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h1, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                rcases p10557_3 (m.d 0 1) (by simp) with h10581 | h10581
                · rcases p10557_3 (m.d 1 2) (by simp) with h10582 | h10582
                  · linarith only [h10364, h10582, hlam]
                  · rcases p10557_3 (m.d 1 3) (by simp) with h10584 | h10584
                    · rcases p10557_3 (m.d 1 4) (by simp) with h10585 | h10585
                      · linarith only [h10370, h10585, hlam]
                      · linarith only [h10366, h10585, hlam]
                    · linarith only [h10364, h10584, hlam]
                · linarith only [h0, h10581, hlam]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h1, h10372, h10376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h1, h10372, h10376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h2, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                rcases p10557_3 (m.d 0 1) (by simp) with h10594 | h10594
                · rcases p10557_3 (m.d 1 2) (by simp) with h10595 | h10595
                  · linarith only [h10366, h10595, hlam]
                  · rcases p10557_3 (m.d 1 3) (by simp) with h10597 | h10597
                    · rcases p10557_3 (m.d 1 4) (by simp) with h10598 | h10598
                      · rcases p10557_3 (m.d 1 5) (by simp) with h10599 | h10599
                        · linarith only [h10372, h10599, hlam]
                        · linarith only [h10368, h10599, hlam]
                      · linarith only [h10366, h10598, hlam]
                    · linarith only [h10364, h10597, hlam]
                · linarith only [h0, h10594, hlam]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10370, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h1, h10370, h10372, h10376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h3, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                rcases p10557_3 (m.d 0 1) (by simp) with h10609 | h10609
                · rcases p10557_3 (m.d 1 2) (by simp) with h10610 | h10610
                  · linarith only [h10368, h10610, hlam]
                  · rcases p10557_3 (m.d 1 3) (by simp) with h10612 | h10612
                    · rcases p10557_3 (m.d 1 4) (by simp) with h10613 | h10613
                      · rcases p10557_3 (m.d 1 5) (by simp) with h10614 | h10614
                        · rcases h3bigk with h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c | h10615c
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10370, h10372, h4, hc12, hc23, hlam, hphi, p10557_1, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h4, hlam, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            rcases p10615_3 (m.d 0 3) (by simp) with h10619 | h10619
                            · rcases p10615_3 (m.d 1 3) (by simp) with h10620 | h10620
                              · linarith only [h1, h10620, hlam]
                              · linarith only [h10370, h10620, hlam]
                            · linarith only [h10619, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            rcases p10615_3 (m.d 0 3) (by simp) with h10624 | h10624
                            · rcases p10615_3 (m.d 1 3) (by simp) with h10625 | h10625
                              · linarith only [h1, h10625, hlam]
                              · linarith only [h10371, h10625, hlam]
                            · linarith only [h10624, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h1, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10364, hlam, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            rcases p10615_3 (m.d 0 3) (by simp) with h10632 | h10632
                            · rcases p10615_3 (m.d 1 3) (by simp) with h10633 | h10633
                              · rcases p10615_3 (m.d 2 3) (by simp) with h10634 | h10634
                                · rcases p10615_3 (m.d 3 4) (by simp) with h10635 | h10635
                                  · linarith only [h10635, hlam, p10615_0]
                                  · rcases p10615_3 (m.d 3 5) (by simp) with h10637 | h10637
                                    · linarith only [h10371, h10637, hlam]
                                    · linarith only [h10376, h10637, hlam]
                                · linarith only [h10373, h10634, hlam]
                              · linarith only [h10633, hlam, p10615_0]
                            · linarith only [h10361, h10632, hlam]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            rcases p10615_3 (m.d 0 3) (by simp) with h10643 | h10643
                            · rcases p10615_3 (m.d 1 3) (by simp) with h10644 | h10644
                              · rcases p10615_3 (m.d 2 3) (by simp) with h10645 | h10645
                                · rcases p10615_3 (m.d 3 4) (by simp) with h10646 | h10646
                                  · linarith only [h10370, h10646, hlam]
                                  · rcases p10615_3 (m.d 3 5) (by simp) with h10648 | h10648
                                    · linarith only [h10648, hlam, p10615_0]
                                    · rcases h5bigk with h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c | h10650c
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10363, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10557_1, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h9870, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        rcases p10650_3 (m.d 0 5) (by simp) with h10654 | h10654
                                        · rcases p10650_3 (m.d 1 5) (by simp) with h10655 | h10655
                                          · linarith only [h10655, h3, hlam]
                                          · linarith only [h10371, h10655, hlam]
                                        · linarith only [h10362, h10654, hlam]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10361, h10363, h10376, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h3, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10368, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h1, h10370, h10372, hc01, hc35, hlam, hphi, ht0b, ht5b, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h1, h10370, h10372, h10376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h3, hc12, hc25, hlam, hphi, p10557_1, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [hc12, hc25, hlam, hphi, p10557_1, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        rcases p10650_3 (m.d 0 5) (by simp) with h10668 | h10668
                                        · linarith only [h10668, h9870, hlam]
                                        · linarith only [h10362, h10668, hlam]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h1, h10370, h10372, h10373, h10375, h10376, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10362, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10371, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10374, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10376, hlam, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10363, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10372, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10375, hlam, p10650_0]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [h10376, hc34, hc45, hlam, hphi, p10650_1]
                                      · have p10650_0 := h10650c.1
                                        have p10650_1 := h10650c.2.1
                                        have p10650_2 := h10650c.2.2.1
                                        have p10650_3 := h10650c.2.2.2
                                        linarith only [hlam, p10650_0]
                                · linarith only [h10374, h10645, hlam]
                              · linarith only [h10644, hlam, p10615_0]
                            · linarith only [h10362, h10643, hlam]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h1, h10370, h10372, hc12, hc23, hlam, hphi, p10557_1, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10370, h10372, hc12, hc23, hlam, hphi, p10557_1, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            rcases p10615_3 (m.d 0 3) (by simp) with h10688 | h10688
                            · linarith only [h10688, h4, hlam]
                            · linarith only [h10361, h10688, hlam]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            rcases p10615_3 (m.d 0 3) (by simp) with h10691 | h10691
                            · linarith only [h10691, h4, hlam]
                            · linarith only [h10362, h10691, hlam]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10361, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10370, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10373, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10376, hlam, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10362, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10371, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h10374, hlam, p10615_0]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [h1, h10371, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10615_1]
                          · have p10615_0 := h10615c.1
                            have p10615_1 := h10615c.2.1
                            have p10615_2 := h10615c.2.2.1
                            have p10615_3 := h10615c.2.2.2
                            linarith only [hlam, p10615_0]
                        · linarith only [h10368, h10614, hlam]
                      · linarith only [h10366, h10613, hlam]
                    · linarith only [h10364, h10612, hlam]
                · linarith only [h0, h10609, hlam]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10371, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [h10372, hlam, p10557_0]
              · have p10557_0 := h10557c.1
                have p10557_1 := h10557c.2.1
                have p10557_2 := h10557c.2.2.1
                have p10557_3 := h10557c.2.2.2
                linarith only [hlam, p10557_0]
          · linarith only [h0, h1, h10370, h10372, h10375, h8674, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h1, h10371, h10374, h4, hlam]
      · linarith only [h10361, h10373, h4, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h10714 | h10714
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10715 | h10715
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10716 | h10716
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10717 | h10717
            · linarith only [h10370, h10372, h10717, hlam]
            · rcases h1bigk with h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c | h10719c
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10721 | h10721
                · rcases p10719_3 (m.d 1 2) (by simp) with h10722 | h10722
                  · linarith only [h10722, hlam, p10719_0]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10724 | h10724
                    · linarith only [h1, h10724, hlam]
                    · linarith only [h10364, h10724, hlam]
                · linarith only [h10721, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10728 | h10728
                · rcases p10719_3 (m.d 1 2) (by simp) with h10729 | h10729
                  · linarith only [h0, h10729, hlam]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10731 | h10731
                    · linarith only [h10731, hlam, p10719_0]
                    · rcases p10719_3 (m.d 1 4) (by simp) with h10733 | h10733
                      · linarith only [h10733, h2, hlam]
                      · rcases p10719_3 (m.d 1 5) (by simp) with h10735 | h10735
                        · linarith only [h10735, h3, hlam]
                        · rcases h3bigk with h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c | h10737c
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            rcases p10737_3 (m.d 0 3) (by simp) with h10739 | h10739
                            · rcases p10737_3 (m.d 1 3) (by simp) with h10740 | h10740
                              · linarith only [h1, h10740, hlam]
                              · rcases p10737_3 (m.d 2 3) (by simp) with h10742 | h10742
                                · rcases p10737_3 (m.d 3 4) (by simp) with h10743 | h10743
                                  · linarith only [h10361, h10743, hlam]
                                  · rcases p10737_3 (m.d 3 5) (by simp) with h10745 | h10745
                                    · linarith only [h10362, h10745, hlam]
                                    · rcases h5bigk with h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c | h10747c
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10366, h10372, h10716, h9870, hc12, hc24, hlam, hphi, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h9870, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        rcases p10747_3 (m.d 0 5) (by simp) with h10751 | h10751
                                        · rcases p10747_3 (m.d 1 5) (by simp) with h10752 | h10752
                                          · linarith only [h10752, h3, hlam]
                                          · linarith only [h10371, h10752, hlam]
                                        · linarith only [h10362, h10751, hlam]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10361, h10363, h10366, h10372, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h3, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10368, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10717, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10372, hlam, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h0, h10714, h10716, h9870, hc12, hc23, hlam, hphi, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10368, h10714, h10716, hc12, hc23, hlam, hphi, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        rcases p10747_3 (m.d 0 5) (by simp) with h10765 | h10765
                                        · linarith only [h10765, h9870, hlam]
                                        · linarith only [h10362, h10765, hlam]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10366, h10372, h10714, h10716, hc12, hc23, hlam, hphi, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10362, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10371, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10715, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10717, hlam, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10363, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10366, h10372, hc12, hc45, hlam, hphi, ht23, ht34, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10716, hlam, p10747_0]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [h10361, h10363, h10717, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10747_1]
                                      · have p10747_0 := h10747c.1
                                        have p10747_1 := h10747c.2.1
                                        have p10747_2 := h10747c.2.2.1
                                        have p10747_3 := h10747c.2.2.2
                                        linarith only [hlam, p10747_0]
                                · linarith only [h10364, h10742, hlam]
                            · linarith only [h1, h10739, hlam]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h4, hlam, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            rcases p10737_3 (m.d 0 3) (by simp) with h10782 | h10782
                            · rcases p10737_3 (m.d 1 3) (by simp) with h10783 | h10783
                              · linarith only [h1, h10783, hlam]
                              · linarith only [h10370, h10783, hlam]
                            · linarith only [h10782, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            rcases p10737_3 (m.d 0 3) (by simp) with h10787 | h10787
                            · rcases p10737_3 (m.d 1 3) (by simp) with h10788 | h10788
                              · linarith only [h1, h10788, hlam]
                              · linarith only [h10371, h10788, hlam]
                            · linarith only [h10787, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h1, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10364, hlam, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10719_1, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10719_1, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10361, h10363, h10366, h10372, hc12, hc23, hlam, hphi, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            rcases p10737_3 (m.d 0 3) (by simp) with h10798 | h10798
                            · linarith only [h10798, h4, hlam]
                            · linarith only [h1, h10798, hlam]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            rcases p10737_3 (m.d 0 3) (by simp) with h10802 | h10802
                            · linarith only [h10802, h4, hlam]
                            · linarith only [h10361, h10802, hlam]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            rcases p10737_3 (m.d 0 3) (by simp) with h10805 | h10805
                            · linarith only [h10805, h4, hlam]
                            · linarith only [h10362, h10805, hlam]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10361, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10370, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10714, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10717, hlam, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10362, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10371, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10715, hlam, p10737_0]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [h10371, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10719_1, p10737_1]
                          · have p10737_0 := h10737c.1
                            have p10737_1 := h10737c.2.1
                            have p10737_2 := h10737c.2.2.1
                            have p10737_3 := h10737c.2.2.2
                            linarith only [hlam, p10737_0]
                · linarith only [h10728, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10819 | h10819
                · rcases p10719_3 (m.d 1 2) (by simp) with h10820 | h10820
                  · linarith only [h0, h10820, hlam]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10822 | h10822
                    · linarith only [h1, h10822, hlam]
                    · linarith only [h10370, h10822, hlam]
                · linarith only [h10819, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10826 | h10826
                · rcases p10719_3 (m.d 1 2) (by simp) with h10827 | h10827
                  · linarith only [h0, h10827, hlam]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10829 | h10829
                    · linarith only [h1, h10829, hlam]
                    · linarith only [h10371, h10829, hlam]
                · linarith only [h10826, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h0, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10364, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10366, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10368, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h1, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10839 | h10839
                · rcases p10719_3 (m.d 1 2) (by simp) with h10840 | h10840
                  · linarith only [h10364, h10840, hlam]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10842 | h10842
                    · rcases p10719_3 (m.d 1 4) (by simp) with h10843 | h10843
                      · linarith only [h10370, h10843, hlam]
                      · linarith only [h10366, h10843, hlam]
                    · linarith only [h10364, h10842, hlam]
                · linarith only [h0, h10839, hlam]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10849 | h10849
                · rcases p10719_3 (m.d 1 2) (by simp) with h10850 | h10850
                  · linarith only [h10364, h10850, hlam]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10852 | h10852
                    · rcases p10719_3 (m.d 1 4) (by simp) with h10853 | h10853
                      · linarith only [h10370, h10853, hlam]
                      · rcases p10719_3 (m.d 1 5) (by simp) with h10855 | h10855
                        · linarith only [h10371, h10855, hlam]
                        · linarith only [h10372, h10855, hlam]
                    · linarith only [h10370, h10852, hlam]
                · linarith only [h10849, h2, hlam]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                rcases p10719_3 (m.d 0 1) (by simp) with h10860 | h10860
                · rcases p10719_3 (m.d 1 2) (by simp) with h10861 | h10861
                  · linarith only [h10364, h10861, hlam]
                  · rcases p10719_3 (m.d 1 3) (by simp) with h10863 | h10863
                    · rcases p10719_3 (m.d 1 4) (by simp) with h10864 | h10864
                      · linarith only [h10370, h10864, hlam]
                      · rcases p10719_3 (m.d 1 5) (by simp) with h10866 | h10866
                        · linarith only [h10371, h10866, hlam]
                        · rcases h3bigk with h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c | h10868c
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10366, h10372, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10719_1, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h4, hlam, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            rcases p10868_3 (m.d 0 3) (by simp) with h10872 | h10872
                            · rcases p10868_3 (m.d 1 3) (by simp) with h10873 | h10873
                              · linarith only [h1, h10873, hlam]
                              · linarith only [h10370, h10873, hlam]
                            · linarith only [h10872, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            rcases p10868_3 (m.d 0 3) (by simp) with h10877 | h10877
                            · rcases p10868_3 (m.d 1 3) (by simp) with h10878 | h10878
                              · linarith only [h1, h10878, hlam]
                              · linarith only [h10371, h10878, hlam]
                            · linarith only [h10877, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h1, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10364, hlam, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            rcases p10868_3 (m.d 0 3) (by simp) with h10885 | h10885
                            · rcases p10868_3 (m.d 1 3) (by simp) with h10886 | h10886
                              · rcases p10868_3 (m.d 2 3) (by simp) with h10887 | h10887
                                · rcases p10868_3 (m.d 3 4) (by simp) with h10888 | h10888
                                  · linarith only [h10888, hlam, p10868_0]
                                  · rcases p10868_3 (m.d 3 5) (by simp) with h10890 | h10890
                                    · linarith only [h10371, h10890, hlam]
                                    · linarith only [h10717, h10890, hlam]
                                · linarith only [h10714, h10887, hlam]
                              · linarith only [h10886, hlam, p10868_0]
                            · linarith only [h10361, h10885, hlam]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            rcases p10868_3 (m.d 0 3) (by simp) with h10896 | h10896
                            · rcases p10868_3 (m.d 1 3) (by simp) with h10897 | h10897
                              · rcases p10868_3 (m.d 2 3) (by simp) with h10898 | h10898
                                · rcases p10868_3 (m.d 3 4) (by simp) with h10899 | h10899
                                  · linarith only [h10370, h10899, hlam]
                                  · rcases p10868_3 (m.d 3 5) (by simp) with h10901 | h10901
                                    · linarith only [h10901, hlam, p10868_0]
                                    · rcases h5bigk with h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c | h10903c
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10363, h10366, h10372, h10714, h8674, hc12, hc23, hlam, hphi, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h9870, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        rcases p10903_3 (m.d 0 5) (by simp) with h10907 | h10907
                                        · rcases p10903_3 (m.d 1 5) (by simp) with h10908 | h10908
                                          · linarith only [h10908, h3, hlam]
                                          · linarith only [h10371, h10908, hlam]
                                        · linarith only [h10362, h10907, hlam]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10363, h10366, h10372, h10714, h8674, hc12, hc23, hlam, hphi, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h3, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10368, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10717, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10719_1, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10372, hlam, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h0, h10714, h10716, h9870, hc12, hc23, hlam, hphi, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10368, h10714, h10716, hc12, hc23, hlam, hphi, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        rcases p10903_3 (m.d 0 5) (by simp) with h10921 | h10921
                                        · linarith only [h10921, h9870, hlam]
                                        · linarith only [h10362, h10921, hlam]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10366, h10372, h10714, h10716, hc12, hc23, hlam, hphi, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10362, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10371, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10715, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10717, hlam, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10363, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10363, h10366, h10372, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10716, hlam, p10903_0]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [h10363, h10714, h10717, h8674, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10903_1]
                                      · have p10903_0 := h10903c.1
                                        have p10903_1 := h10903c.2.1
                                        have p10903_2 := h10903c.2.2.1
                                        have p10903_3 := h10903c.2.2.2
                                        linarith only [hlam, p10903_0]
                                · linarith only [h10715, h10898, hlam]
                              · linarith only [h10897, hlam, p10868_0]
                            · linarith only [h10362, h10896, hlam]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h1, h10366, h10372, hc12, hc23, hlam, hphi, p10719_1, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10366, h10372, hc12, hc23, hlam, hphi, p10719_1, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            rcases p10868_3 (m.d 0 3) (by simp) with h10941 | h10941
                            · linarith only [h10941, h4, hlam]
                            · linarith only [h10361, h10941, hlam]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            rcases p10868_3 (m.d 0 3) (by simp) with h10944 | h10944
                            · linarith only [h10944, h4, hlam]
                            · linarith only [h10362, h10944, hlam]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10361, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10370, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10714, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10717, hlam, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10362, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10371, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h10715, hlam, p10868_0]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [h1, h10371, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10868_1]
                          · have p10868_0 := h10868c.1
                            have p10868_1 := h10868c.2.1
                            have p10868_2 := h10868c.2.2.1
                            have p10868_3 := h10868c.2.2.2
                            linarith only [hlam, p10868_0]
                    · linarith only [h10371, h10863, hlam]
                · linarith only [h10860, h3, hlam]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h2, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10361, h10363, h10372, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10719_1]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10370, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10372, hlam, p10719_1]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h3, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10361, h10363, h10372, h4, hc12, hc23, hlam, hphi, p10719_1]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10371, hlam, p10719_0]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [h10361, h10363, h10366, h10372, h4, hc12, hc23, hlam, hphi, p10719_1]
              · have p10719_0 := h10719c.1
                have p10719_1 := h10719c.2.1
                have p10719_2 := h10719c.2.2.1
                have p10719_3 := h10719c.2.2.2
                linarith only [hlam, p10719_0]
          · linarith only [h0, h10361, h10363, h10716, h4, h8674, hc12, hc23, hlam, hphi]
        · linarith only [h1, h10361, h10363, h10371, h10372, h10715, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]
      · linarith only [h10361, h10363, h10366, h10372, h10714, h4, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h10972 | h10972
    · linarith only [h10370, h10371, h10972, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h10974 | h10974
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10975 | h10975
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10976 | h10976
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10977 | h10977
            · linarith only [h10362, h10370, h10371, h10972, h10977, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases h1bigk with h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c | h10979c
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                rcases p10979_3 (m.d 0 1) (by simp) with h10981 | h10981
                · rcases p10979_3 (m.d 1 2) (by simp) with h10982 | h10982
                  · linarith only [h10982, hlam, p10979_0]
                  · rcases p10979_3 (m.d 1 3) (by simp) with h10984 | h10984
                    · linarith only [h1, h10984, hlam]
                    · linarith only [h10364, h10984, hlam]
                · linarith only [h10981, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                rcases p10979_3 (m.d 0 1) (by simp) with h10988 | h10988
                · rcases p10979_3 (m.d 1 2) (by simp) with h10989 | h10989
                  · linarith only [h0, h10989, hlam]
                  · rcases p10979_3 (m.d 1 3) (by simp) with h10991 | h10991
                    · linarith only [h10991, hlam, p10979_0]
                    · rcases p10979_3 (m.d 1 4) (by simp) with h10993 | h10993
                      · linarith only [h10993, h2, hlam]
                      · rcases p10979_3 (m.d 1 5) (by simp) with h10995 | h10995
                        · linarith only [h10995, h3, hlam]
                        · linarith only [h10371, h10995, hlam]
                · linarith only [h10988, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                rcases p10979_3 (m.d 0 1) (by simp) with h10999 | h10999
                · rcases p10979_3 (m.d 1 2) (by simp) with h11000 | h11000
                  · linarith only [h0, h11000, hlam]
                  · rcases p10979_3 (m.d 1 3) (by simp) with h11002 | h11002
                    · linarith only [h1, h11002, hlam]
                    · linarith only [h10370, h11002, hlam]
                · linarith only [h10999, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                rcases p10979_3 (m.d 0 1) (by simp) with h11006 | h11006
                · rcases p10979_3 (m.d 1 2) (by simp) with h11007 | h11007
                  · linarith only [h0, h11007, hlam]
                  · rcases p10979_3 (m.d 1 3) (by simp) with h11009 | h11009
                    · linarith only [h1, h11009, hlam]
                    · rcases p10979_3 (m.d 1 4) (by simp) with h11011 | h11011
                      · linarith only [h11011, h2, hlam]
                      · rcases p10979_3 (m.d 1 5) (by simp) with h11013 | h11013
                        · linarith only [h11013, hlam, p10979_0]
                        · rcases h3bigk with h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c | h11015c
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            rcases p11015_3 (m.d 0 3) (by simp) with h11017 | h11017
                            · rcases p11015_3 (m.d 1 3) (by simp) with h11018 | h11018
                              · linarith only [h1, h11018, hlam]
                              · rcases p11015_3 (m.d 2 3) (by simp) with h11020 | h11020
                                · rcases p11015_3 (m.d 3 4) (by simp) with h11021 | h11021
                                  · linarith only [h10361, h11021, hlam]
                                  · rcases p11015_3 (m.d 3 5) (by simp) with h11023 | h11023
                                    · linarith only [h10362, h11023, hlam]
                                    · linarith only [h10371, h11023, hlam]
                                · linarith only [h10364, h11020, hlam]
                            · linarith only [h1, h11017, hlam]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h4, hlam, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10361, h10363, h10370, h10371, h10977, hlam, p11015_2]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10370, h10371, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h1, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10364, hlam, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10371, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10979_1, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10371, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10362, h10371, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            rcases p11015_3 (m.d 0 3) (by simp) with h11037 | h11037
                            · linarith only [h11037, h4, hlam]
                            · linarith only [h1, h11037, hlam]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10361, h10363, h10370, h10371, h10977, h4, hlam, p11015_2]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10370, h10371, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10361, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10370, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10974, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10977, hlam, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10362, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10361, h10363, h10370, h10977, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11015_1]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [h10975, hlam, p11015_0]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            rcases p11015_3 (m.d 0 3) (by simp) with h11051 | h11051
                            · rcases p11015_3 (m.d 1 3) (by simp) with h11052 | h11052
                              · linarith only [h10371, h11052, hlam]
                              · linarith only [h10370, h11052, hlam]
                            · linarith only [h10361, h11051, hlam]
                          · have p11015_0 := h11015c.1
                            have p11015_1 := h11015c.2.1
                            have p11015_2 := h11015c.2.2.1
                            have p11015_3 := h11015c.2.2.2
                            linarith only [hlam, p11015_0]
                · linarith only [h11006, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h0, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10364, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10366, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10368, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h1, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10361, h10363, h10371, h10977, h4, hc12, hc23, hlam, hphi, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10361, h10363, h10366, h10371, h10977, h4, hc12, hc23, hlam, hphi, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10371, hlam, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h2, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10361, h10363, h10370, h10371, h10977, h4, hc12, hc23, hlam, hphi, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10370, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10972, hlam, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h3, hlam, p10979_0]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10361, h10363, h10371, h10977, h4, hc12, hc23, hlam, hphi, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10361, h10363, h10364, h10371, h10977, h4, hc12, hc23, hlam, hphi, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [h10361, h10363, h10366, h10371, h10977, h4, hc12, hc23, hlam, hphi, p10979_1]
              · have p10979_0 := h10979c.1
                have p10979_1 := h10979c.2.1
                have p10979_2 := h10979c.2.2.1
                have p10979_3 := h10979c.2.2.2
                linarith only [hlam, p10979_0]
          · linarith only [h0, h10361, h10363, h10976, h4, h8674, hc12, hc23, hlam, hphi]
        · linarith only [h10362, h10975, h4, hlam]
      · linarith only [h1, h10361, h10363, h10370, h10974, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]

end R2N4
