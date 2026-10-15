import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S3
import Jsp000404.R1LeavesN7_12S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 7030000 in
set_option maxHeartbeats 7030000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3378 | h3378
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3379 | h3379
      · linarith only [h3378, h3379, h4, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3381 | h3381
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3382 | h3382
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3383 | h3383
            · linarith only [h0, h3383, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3385 | h3385
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3386 | h3386
                · linarith only [h3381, h3383, h3386, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3388 | h3388
                  · linarith only [h2, h3379, h3388, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3390 | h3390
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3391 | h3391
                      · linarith only [h3386, h3391, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3393 | h3393
                        · linarith only [h3379, h3391, h3393, h5, h6, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h3381, h3390, h3393, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h3385, h3386, h3390, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3397 | h3397
                · linarith only [h3378, h3385, h3397, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3399 | h3399
                  · linarith only [h3378, h3385, h3399, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3401 | h3401
                    · linarith only [h3381, h3385, h3401, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3403 | h3403
                      · linarith only [h3378, h3381, h3385, h3397, h3403, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h3378, h3385, h3403, h4, h6, hc13, hc35, hlam, hphi]
          · linarith only [h3382, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h3381, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3408 | h3408
      · linarith only [h3408, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3410 | h3410
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3411 | h3411
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3412 | h3412
            · linarith only [h0, h3412, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3414 | h3414
              · linarith only [h1, h3378, h3414, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3416 | h3416
                · linarith only [h3410, h3412, h3416, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3418 | h3418
                  · linarith only [h2, h3408, h3418, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3420 | h3420
                    · linarith only [h1, h3378, h3410, h3420, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3422 | h3422
                      · linarith only [h3411, h3412, h3416, h3420, h3422, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3424 | h3424
                        · linarith only [h0, h3408, h3411, h3424, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3426 | h3426
                          · linarith only [h0, h3411, h3420, h3424, h3426, h6, hc23, hc34, hlam, hphi]
                          · rcases h1bigk with h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c | h3428c
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              rcases p3428_3 (m.d 0 1) (by simp) with h3430 | h3430
                              · rcases p3428_3 (m.d 1 2) (by simp) with h3431 | h3431
                                · linarith only [h3431, hlam, p3428_0]
                                · rcases p3428_3 (m.d 1 3) (by simp) with h3433 | h3433
                                  · linarith only [h1, h3433, hlam]
                                  · rcases p3428_3 (m.d 1 4) (by simp) with h3435 | h3435
                                    · linarith only [h2, h3435, hlam]
                                    · rcases p3428_3 (m.d 1 5) (by simp) with h3437 | h3437
                                      · linarith only [h3, h3437, hlam]
                                      · linarith only [h3412, h3437, hlam]
                              · linarith only [h3430, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              rcases p3428_3 (m.d 0 1) (by simp) with h3441 | h3441
                              · rcases p3428_3 (m.d 1 2) (by simp) with h3442 | h3442
                                · linarith only [h0, h3442, hlam]
                                · linarith only [h3410, h3442, hlam]
                              · linarith only [h3441, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              rcases p3428_3 (m.d 0 1) (by simp) with h3446 | h3446
                              · rcases p3428_3 (m.d 1 2) (by simp) with h3447 | h3447
                                · linarith only [h0, h3447, hlam]
                                · linarith only [h3411, h3447, hlam]
                              · linarith only [h3446, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              rcases p3428_3 (m.d 0 1) (by simp) with h3451 | h3451
                              · rcases p3428_3 (m.d 1 2) (by simp) with h3452 | h3452
                                · linarith only [h0, h3452, hlam]
                                · rcases p3428_3 (m.d 1 3) (by simp) with h3454 | h3454
                                  · linarith only [h1, h3454, hlam]
                                  · rcases p3428_3 (m.d 1 4) (by simp) with h3456 | h3456
                                    · linarith only [h2, h3456, hlam]
                                    · rcases p3428_3 (m.d 1 5) (by simp) with h3458 | h3458
                                      · linarith only [h3458, hlam, p3428_0]
                                      · rcases h2bigk with h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3411, h3420, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3422, h6, hc23, hc35, hlam, hphi, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3420, h3422, h6, hc23, hc35, hlam, hphi, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h6, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h0, hlam, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3412, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3428_1, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3412, h3420, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3428_1, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3412, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h4, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3410, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3420, hlam, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3422, hlam, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h5, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3411, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3422, h5, h6, hc23, hc35, hlam, hphi, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3424, hlam, p3460_0]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3422, h4, hc23, hc35, hlam, hphi, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [h3410, h3422, hc23, hc35, hlam, hphi, p3460_1]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          rcases p3460_3 (m.d 0 2) (by simp) with h3483 | h3483
                                          · linarith only [h3483, h6, hlam]
                                          · linarith only [h3483, h4, hlam]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          rcases p3460_3 (m.d 0 2) (by simp) with h3486 | h3486
                                          · linarith only [h3486, h6, hlam]
                                          · linarith only [h3486, h5, hlam]
                                        · have p3460_0 := h3460c.1
                                          have p3460_1 := h3460c.2.1
                                          have p3460_2 := h3460c.2.2.1
                                          have p3460_3 := h3460c.2.2.2
                                          linarith only [hlam, p3460_0]
                              · linarith only [h3451, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h0, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h0, h3410, h3422, h3426, h6, hc23, hc45, hlam, hphi, ht34, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h0, h3410, h3414, h3422, h3426, h6, hc23, hc45, hlam, hphi, ht34, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3412, hlam, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h1, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3410, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3414, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3416, hlam, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h2, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3411, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h2, h3410, h3422, h3426, h5, h6, hc23, hc45, hlam, hphi, ht34, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3418, hlam, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3, hlam, p3428_0]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [h3, h3410, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3428_1]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              rcases p3428_3 (m.d 0 1) (by simp) with h3508 | h3508
                              · rcases p3428_3 (m.d 1 2) (by simp) with h3509 | h3509
                                · linarith only [h3412, h3509, hlam]
                                · linarith only [h3410, h3509, hlam]
                              · linarith only [h1, h3508, hlam]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              rcases p3428_3 (m.d 0 1) (by simp) with h3513 | h3513
                              · rcases p3428_3 (m.d 1 2) (by simp) with h3514 | h3514
                                · linarith only [h3412, h3514, hlam]
                                · linarith only [h3411, h3514, hlam]
                              · linarith only [h2, h3513, hlam]
                            · have p3428_0 := h3428c.1
                              have p3428_1 := h3428c.2.1
                              have p3428_2 := h3428c.2.2.1
                              have p3428_3 := h3428c.2.2.2
                              linarith only [hlam, p3428_0]
          · linarith only [h3411, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h3410, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 7362000 in
set_option maxHeartbeats 7362000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s5 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3521 | h3521
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3522 | h3522
      · linarith only [h3522, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3524 | h3524
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3525 | h3525
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3526 | h3526
            · linarith only [h0, h3526, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3528 | h3528
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3529 | h3529
                · linarith only [h1, h3522, h3529, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3531 | h3531
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3532 | h3532
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3533 | h3533
                      · linarith only [h0, h3522, h3525, h3533, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3535 | h3535
                        · linarith only [h0, h3525, h3533, h3535, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1, h3531, h3533, h3535, h4, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h3522, h3524, h3525, h3526, h3532, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3539 | h3539
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3540 | h3540
                      · linarith only [h0, h2, h3522, h3526, h3528, h3540, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3542 | h3542
                        · linarith only [h3531, h3542, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3544 | h3544
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3545 | h3545
                            · rcases h1bigk with h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c | h3546c
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3528, h3544, hc01, hlam, hphi, ht0b, ht5b, p3546_1, u5ehi4]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                rcases p3546_3 (m.d 0 1) (by simp) with h3549 | h3549
                                · rcases p3546_3 (m.d 1 2) (by simp) with h3550 | h3550
                                  · linarith only [h0, h3550, hlam]
                                  · linarith only [h3525, h3550, hlam]
                                · linarith only [h3549, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3526, h3528, h3544, hc01, hlam, hphi, ht0b, ht5b, p3546_1, u5ehi4]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                rcases p3546_3 (m.d 0 1) (by simp) with h3555 | h3555
                                · rcases p3546_3 (m.d 1 2) (by simp) with h3556 | h3556
                                  · linarith only [h0, h3556, hlam]
                                  · linarith only [h3528, h3556, hlam]
                                · linarith only [h3555, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h0, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h0, h3540, h5, hc13, hc34, hlam, hphi, p3546_1]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3526, hlam, p3546_1]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h0, h3540, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3546_1, u5ehi1]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h1, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3525, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3529, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3531, hlam, p3546_1]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h2, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h2, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3546_1]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                rcases p3546_3 (m.d 0 1) (by simp) with h3572 | h3572
                                · rcases p3546_3 (m.d 1 2) (by simp) with h3573 | h3573
                                  · linarith only [h3526, h3573, hlam]
                                  · linarith only [h3525, h3573, hlam]
                                · linarith only [h1, h3572, hlam]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h2, h3528, h3544, hc01, hlam, hphi, ht0b, ht5b, p3546_1, u5ehi4]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3528, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3, h3521, h3525, h3540, h5, hc23, hc34, hlam, hphi, p3546_1]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [h3539, hlam, p3546_0]
                              · have p3546_0 := h3546c.1
                                have p3546_1 := h3546c.2.1
                                have p3546_2 := h3546c.2.2.1
                                have p3546_3 := h3546c.2.2.2
                                linarith only [hlam, p3546_0]
                            · linarith only [h0, h3528, h3540, h3544, h3545, h5, hlam]
                          · linarith only [h0, h3528, h3544, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h3521, h3524, h3526, h3528, h3539, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h3521, h3528, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3525, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h3521, h3524, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3590 | h3590
      · linarith only [h3590, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3592 | h3592
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3593 | h3593
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3594 | h3594
            · linarith only [h0, h3594, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3596 | h3596
              · linarith only [h0, h3521, h3596, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3598 | h3598
                · linarith only [h1, h3590, h3598, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3600 | h3600
                  · linarith only [h3593, h3596, h3600, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3602 | h3602
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3603 | h3603
                      · linarith only [h0, h3590, h3593, h3603, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3605 | h3605
                        · linarith only [h0, h3593, h3603, h3605, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3607 | h3607
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3608 | h3608
                            · rcases h1bigk with h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3611 | h3611
                                · rcases p3609_3 (m.d 1 2) (by simp) with h3612 | h3612
                                  · linarith only [h3612, hlam, p3609_0]
                                  · rcases p3609_3 (m.d 1 3) (by simp) with h3614 | h3614
                                    · linarith only [h1, h3614, hlam]
                                    · rcases p3609_3 (m.d 1 4) (by simp) with h3616 | h3616
                                      · linarith only [h2, h3616, hlam]
                                      · linarith only [h3594, h3616, hlam]
                                · linarith only [h3611, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3620 | h3620
                                · rcases p3609_3 (m.d 1 2) (by simp) with h3621 | h3621
                                  · linarith only [h0, h3621, hlam]
                                  · linarith only [h3593, h3621, hlam]
                                · linarith only [h3620, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3602, hc01, hlam, hphi, ht0b, ht5b, p3609_1, u5ehi4]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3626 | h3626
                                · rcases p3609_3 (m.d 1 2) (by simp) with h3627 | h3627
                                  · linarith only [h0, h3627, hlam]
                                  · rcases p3609_3 (m.d 1 3) (by simp) with h3629 | h3629
                                    · linarith only [h1, h3629, hlam]
                                    · rcases p3609_3 (m.d 1 4) (by simp) with h3631 | h3631
                                      · linarith only [h2, h3631, hlam]
                                      · linarith only [h3602, h3631, hlam]
                                · linarith only [h3626, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h0, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h0, h3521, h3603, h3607, hc13, hc34, hlam, hphi, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3594, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3596, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h1, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3593, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3598, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3600, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h2, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h2, h3593, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3647 | h3647
                                · rcases p3609_3 (m.d 1 2) (by simp) with h3648 | h3648
                                  · linarith only [h3594, h3648, hlam]
                                  · linarith only [h3593, h3648, hlam]
                                · linarith only [h1, h3647, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h2, h3593, h3596, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3, h3593, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3656 | h3656
                                · rcases p3609_3 (m.d 1 2) (by simp) with h3657 | h3657
                                  · linarith only [h3596, h3657, hlam]
                                  · linarith only [h3593, h3657, hlam]
                                · linarith only [h1, h3656, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3602, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                            · linarith only [h0, h3521, h3593, h3603, h3607, h3608, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h2, h3602, h3607, h5, hlam]
                    · linarith only [h3590, h3592, h3593, h3594, h3602, hc23, hc34, hlam, hphi]
          · linarith only [h3521, h3593, h4, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3667 | h3667
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3668 | h3668
            · linarith only [h0, h3668, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3670 | h3670
              · linarith only [h0, h3521, h3670, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3672 | h3672
                · linarith only [h1, h3590, h3672, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3674 | h3674
                  · linarith only [h3667, h3670, h3674, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3676 | h3676
                    · linarith only [h2, h3592, h3676, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3678 | h3678
                      · linarith only [h3590, h3678, h4, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3680 | h3680
                        · linarith only [h0, h3667, h3674, h3680, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3682 | h3682
                          · linarith only [h0, h3592, h3667, h3678, h3682, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h3667, h3682, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h3667, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s4 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3687 | h3687
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3688 | h3688
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3689 | h3689
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3690 | h3690
        · linarith only [h0, h3690, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3692 | h3692
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3693 | h3693
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3694 | h3694
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3695 | h3695
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3696 | h3696
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3697 | h3697
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3698 | h3698
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3699 | h3699
                        · linarith only [h3686, h3699, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3701 | h3701
                          · linarith only [h3697, h3699, h3701, hlam]
                          · rcases h1bigk with h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3692, h3696, h3697, h3699, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3690, h3692, h3696, h3697, h3699, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3696, h3697, h3699, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              rcases p3703_3 (m.d 0 1) (by simp) with h3708 | h3708
                              · rcases p3703_3 (m.d 1 2) (by simp) with h3709 | h3709
                                · linarith only [h0, h3709, hlam]
                                · linarith only [h3693, h3709, hlam]
                              · linarith only [h3708, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h0, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3690, hlam, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3696, h3697, h3699, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3703_1, u5ehi1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h1, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h1, h3692, h3697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h1, h3696, h3697, h3699, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h1, h3693, h3698, hc01, hlam, hphi, ht0b, ht5b, p3703_1, u5ehi3]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h2, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3692, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3694, hlam, p3703_1]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h0, h3692, h3693, h3698, hc01, hlam, hphi, ht0b, ht5b, p3703_1, u5ehi3]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3693, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3695, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [h3696, hlam, p3703_0]
                            · have p3703_0 := h3703c.1
                              have p3703_1 := h3703c.2.1
                              have p3703_2 := h3703c.2.2.1
                              have p3703_3 := h3703c.2.2.2
                              linarith only [hlam, p3703_0]
                      · linarith only [h3687, h3698, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h3692, h3696, h3697, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3735 | h3735
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3736 | h3736
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3737 | h3737
                        · linarith only [h3692, h3696, h3737, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3739 | h3739
                          · linarith only [h3692, h3696, h3735, h3739, hlam]
                          · rcases h1bigk with h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c | h3741c
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3693, h3736, hc01, hlam, hphi, ht0b, ht5b, p3741_1, u5ehi3]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3690, h3693, h3736, hc01, hlam, hphi, ht0b, ht5b, p3741_1, u5ehi3]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              rcases p3741_3 (m.d 0 1) (by simp) with h3745 | h3745
                              · rcases p3741_3 (m.d 1 2) (by simp) with h3746 | h3746
                                · linarith only [h0, h3746, hlam]
                                · linarith only [h3692, h3746, hlam]
                              · linarith only [h3745, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              rcases p3741_3 (m.d 0 1) (by simp) with h3750 | h3750
                              · rcases p3741_3 (m.d 1 2) (by simp) with h3751 | h3751
                                · linarith only [h0, h3751, hlam]
                                · linarith only [h3693, h3751, hlam]
                              · linarith only [h3750, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h0, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3690, hlam, p3741_1]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              rcases p3741_3 (m.d 0 1) (by simp) with h3758 | h3758
                              · rcases p3741_3 (m.d 1 2) (by simp) with h3759 | h3759
                                · rcases p3741_3 (m.d 1 3) (by simp) with h3760 | h3760
                                  · rcases p3741_3 (m.d 1 4) (by simp) with h3761 | h3761
                                    · linarith only [h3692, h3761, hlam]
                                    · rcases p3741_3 (m.d 1 5) (by simp) with h3763 | h3763
                                      · linarith only [h3693, h3763, hlam]
                                      · linarith only [h3696, h3763, hlam]
                                  · linarith only [h3694, h3760, hlam]
                                · linarith only [h3692, h3759, hlam]
                              · linarith only [h2, h3758, hlam]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h1, h3690, h3693, h3736, hc01, hlam, hphi, ht0b, ht5b, p3741_1, u5ehi3]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h1, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h1, h3692, h3735, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3741_1]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              rcases p3741_3 (m.d 0 1) (by simp) with h3773 | h3773
                              · rcases p3741_3 (m.d 1 2) (by simp) with h3774 | h3774
                                · linarith only [h3690, h3774, hlam]
                                · linarith only [h3692, h3774, hlam]
                              · linarith only [h2, h3773, hlam]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h1, h3693, h3736, hc01, hlam, hphi, ht0b, ht5b, p3741_1, u5ehi3]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h2, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3692, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3694, hlam, p3741_1]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3696, hlam, p3741_1]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3693, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3695, hlam, p3741_0]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [h3686, h3689, h3692, h3696, h3735, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3741_1]
                            · have p3741_0 := h3741c.1
                              have p3741_1 := h3741c.2.1
                              have p3741_2 := h3741c.2.2.1
                              have p3741_3 := h3741c.2.2.2
                              linarith only [hlam, p3741_0]
                      · linarith only [h3686, h3689, h3696, h3736, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h3686, h3689, h3692, h3696, h3735, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3690, h3693, h3695, hlam]
              · linarith only [h3686, h3688, h3690, h3693, h3694, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h3687, h3693, h4, hc12, hc23, hlam, hphi]
          · linarith only [h3686, h3692, h4, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3795 | h3795
        · linarith only [h0, h3795, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3797 | h3797
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3798 | h3798
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3799 | h3799
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3800 | h3800
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3801 | h3801
                  · linarith only [h2, h3689, h3801, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3803 | h3803
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3804 | h3804
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3805 | h3805
                        · linarith only [h2, h3686, h3689, h3805, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3807 | h3807
                          · linarith only [h3, h3686, h3689, h3803, h3807, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                          · rcases h1bigk with h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3798, h3804, hc01, hlam, hphi, ht0b, ht5b, p3809_1, u5ehi3]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3795, h3798, h3804, hc01, hlam, hphi, ht0b, ht5b, p3809_1, u5ehi3]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              rcases p3809_3 (m.d 0 1) (by simp) with h3813 | h3813
                              · rcases p3809_3 (m.d 1 2) (by simp) with h3814 | h3814
                                · linarith only [h0, h3814, hlam]
                                · linarith only [h3797, h3814, hlam]
                              · linarith only [h3813, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              rcases p3809_3 (m.d 0 1) (by simp) with h3818 | h3818
                              · rcases p3809_3 (m.d 1 2) (by simp) with h3819 | h3819
                                · linarith only [h0, h3819, hlam]
                                · linarith only [h3798, h3819, hlam]
                              · linarith only [h3818, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h0, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3795, hlam, p3809_1]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              rcases p3809_3 (m.d 0 1) (by simp) with h3826 | h3826
                              · rcases p3809_3 (m.d 1 2) (by simp) with h3827 | h3827
                                · rcases p3809_3 (m.d 1 3) (by simp) with h3828 | h3828
                                  · rcases p3809_3 (m.d 1 4) (by simp) with h3829 | h3829
                                    · linarith only [h3797, h3829, hlam]
                                    · rcases p3809_3 (m.d 1 5) (by simp) with h3831 | h3831
                                      · linarith only [h3798, h3831, hlam]
                                      · linarith only [h3801, h3831, hlam]
                                  · linarith only [h3799, h3828, hlam]
                                · linarith only [h3797, h3827, hlam]
                              · linarith only [h2, h3826, hlam]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h0, h3798, h3804, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3809_1, u5ehi3]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h1, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h1, h3797, h3803, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3809_1]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              rcases p3809_3 (m.d 0 1) (by simp) with h3841 | h3841
                              · rcases p3809_3 (m.d 1 2) (by simp) with h3842 | h3842
                                · linarith only [h3795, h3842, hlam]
                                · linarith only [h3797, h3842, hlam]
                              · linarith only [h2, h3841, hlam]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h1, h3798, h3804, hc01, hlam, hphi, ht0b, ht5b, p3809_1, u5ehi3]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h2, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3797, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3799, hlam, p3809_1]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3801, hlam, p3809_1]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3798, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [h3800, hlam, p3809_0]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              rcases p3809_3 (m.d 0 1) (by simp) with h3855 | h3855
                              · rcases p3809_3 (m.d 1 2) (by simp) with h3856 | h3856
                                · rcases p3809_3 (m.d 1 3) (by simp) with h3857 | h3857
                                  · rcases p3809_3 (m.d 1 4) (by simp) with h3858 | h3858
                                    · linarith only [h3801, h3858, hlam]
                                    · rcases p3809_3 (m.d 1 5) (by simp) with h3860 | h3860
                                      · rcases h2bigk with h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c | h3861c
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3797, h3798, h3803, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3809_1, p3861_1]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h4, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          rcases p3861_3 (m.d 0 2) (by simp) with h3865 | h3865
                                          · rcases p3861_3 (m.d 1 2) (by simp) with h3866 | h3866
                                            · linarith only [h0, h3866, hlam]
                                            · linarith only [h3797, h3866, hlam]
                                          · linarith only [h3865, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3804, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3861_1, u5ehi3]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h0, hlam, p3861_1]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3795, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          rcases p3861_3 (m.d 0 2) (by simp) with h3874 | h3874
                                          · rcases p3861_3 (m.d 1 2) (by simp) with h3875 | h3875
                                            · rcases p3861_3 (m.d 2 3) (by simp) with h3876 | h3876
                                              · rcases p3861_3 (m.d 2 4) (by simp) with h3877 | h3877
                                                · linarith only [h3877, hlam, p3861_0]
                                                · rcases p3861_3 (m.d 2 5) (by simp) with h3879 | h3879
                                                  · linarith only [h3798, h3879, hlam]
                                                  · linarith only [h3805, h3879, hlam]
                                              · linarith only [h3803, h3876, hlam]
                                            · linarith only [h3875, hlam, p3861_0]
                                          · linarith only [h3686, h3874, hlam]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h0, h3804, hc01, hlam, hphi, ht0b, ht5b, p3861_1, u5ehi3]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3687, h3804, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3861_1, u5ehi3]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3798, h3804, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3861_1, u5ehi3]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3, h3687, h3797, h4, hlam, p3809_1, p3861_2]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          rcases p3861_3 (m.d 0 2) (by simp) with h3890 | h3890
                                          · linarith only [h3890, h4, hlam]
                                          · linarith only [h3687, h3890, hlam]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3686, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3797, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3803, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3805, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3687, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3798, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3804, hlam, p3861_0]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [h3687, h3803, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3861_1]
                                        · have p3861_0 := h3861c.1
                                          have p3861_1 := h3861c.2.1
                                          have p3861_2 := h3861c.2.2.1
                                          have p3861_3 := h3861c.2.2.2
                                          linarith only [hlam, p3861_0]
                                      · linarith only [h3801, h3860, hlam]
                                  · linarith only [h3799, h3857, hlam]
                                · linarith only [h3797, h3856, hlam]
                              · linarith only [h2, h3855, hlam]
                            · have p3809_0 := h3809c.1
                              have p3809_1 := h3809c.2.1
                              have p3809_2 := h3809c.2.2.1
                              have p3809_3 := h3809c.2.2.2
                              linarith only [hlam, p3809_0]
                      · linarith only [h0, h3798, h3804, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h3798, h3803, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h3795, h3798, h3800, hlam]
              · linarith only [h3688, h3795, h3798, h3799, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h3687, h3798, h4, hc12, hc23, hlam, hphi]
          · linarith only [h3686, h3797, h4, hc12, hc23, hlam, hphi]
    · linarith only [h3686, h3688, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3915 | h3915
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3916 | h3916
      · linarith only [h3686, h3687, h3916, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3918 | h3918
        · linarith only [h0, h3918, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3920 | h3920
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3921 | h3921
            · linarith only [h0, h3687, h3921, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3923 | h3923
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3924 | h3924
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3925 | h3925
                  · linarith only [h2, h3916, h3925, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3927 | h3927
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3928 | h3928
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3929 | h3929
                        · linarith only [h0, h2, h3687, h3916, h3920, h3928, h3929, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3931 | h3931
                          · linarith only [h0, h3687, h3920, h3927, h3929, h3931, hlam]
                          · rcases h1bigk with h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c | h3933c
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              rcases p3933_3 (m.d 0 1) (by simp) with h3935 | h3935
                              · rcases p3933_3 (m.d 1 2) (by simp) with h3936 | h3936
                                · linarith only [h3936, hlam, p3933_0]
                                · rcases p3933_3 (m.d 1 3) (by simp) with h3938 | h3938
                                  · linarith only [h1, h3938, hlam]
                                  · linarith only [h3918, h3938, hlam]
                              · linarith only [h3935, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3924, hc01, hlam, hphi, ht0b, ht5b, p3933_1, u5ehi3]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              rcases p3933_3 (m.d 0 1) (by simp) with h3943 | h3943
                              · rcases p3933_3 (m.d 1 2) (by simp) with h3944 | h3944
                                · linarith only [h0, h3944, hlam]
                                · linarith only [h3920, h3944, hlam]
                              · linarith only [h3943, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              rcases p3933_3 (m.d 0 1) (by simp) with h3948 | h3948
                              · rcases p3933_3 (m.d 1 2) (by simp) with h3949 | h3949
                                · linarith only [h0, h3949, hlam]
                                · rcases p3933_3 (m.d 1 3) (by simp) with h3951 | h3951
                                  · linarith only [h1, h3951, hlam]
                                  · linarith only [h3924, h3951, hlam]
                              · linarith only [h3948, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h0, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3918, hlam, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h0, h3687, h3920, h3927, h3929, hc34, hc45, hlam, hphi, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3921, hlam, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h1, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h1, h3920, h3927, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              rcases p3933_3 (m.d 0 1) (by simp) with h3963 | h3963
                              · rcases p3933_3 (m.d 1 2) (by simp) with h3964 | h3964
                                · linarith only [h3918, h3964, hlam]
                                · linarith only [h3920, h3964, hlam]
                              · linarith only [h2, h3963, hlam]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h1, h3920, h3921, h3927, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h2, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3920, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3923, hlam, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3925, hlam, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3, h3920, h3927, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3933_1]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [h3924, hlam, p3933_0]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              rcases p3933_3 (m.d 0 1) (by simp) with h3977 | h3977
                              · rcases p3933_3 (m.d 1 2) (by simp) with h3978 | h3978
                                · linarith only [h3921, h3978, hlam]
                                · linarith only [h3920, h3978, hlam]
                              · linarith only [h2, h3977, hlam]
                            · have p3933_0 := h3933c.1
                              have p3933_1 := h3933c.2.1
                              have p3933_2 := h3933c.2.2.1
                              have p3933_3 := h3933c.2.2.2
                              linarith only [hlam, p3933_0]
                      · linarith only [h1, h3924, h3928, h4, hlam]
                    · linarith only [h3915, h3927, h4, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3985 | h3985
                  · linarith only [h2, h3916, h3985, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3987 | h3987
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3988 | h3988
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3989 | h3989
                        · linarith only [h3916, h3918, h3920, h3924, h3988, h3989, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3991 | h3991
                          · linarith only [h3687, h3918, h3920, h3924, h3987, h3988, h3989, h3991, hc02, hc23, hlam, hphi]
                          · rcases h1bigk with h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              rcases p3993_3 (m.d 0 1) (by simp) with h3995 | h3995
                              · rcases p3993_3 (m.d 1 2) (by simp) with h3996 | h3996
                                · linarith only [h3996, hlam, p3993_0]
                                · rcases p3993_3 (m.d 1 3) (by simp) with h3998 | h3998
                                  · linarith only [h1, h3998, hlam]
                                  · linarith only [h3918, h3998, hlam]
                              · linarith only [h3995, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              rcases p3993_3 (m.d 0 1) (by simp) with h4002 | h4002
                              · rcases p3993_3 (m.d 1 2) (by simp) with h4003 | h4003
                                · linarith only [h0, h4003, hlam]
                                · rcases p3993_3 (m.d 1 3) (by simp) with h4005 | h4005
                                  · linarith only [h4005, hlam, p3993_0]
                                  · rcases p3993_3 (m.d 1 4) (by simp) with h4007 | h4007
                                    · linarith only [h2, h4007, hlam]
                                    · rcases p3993_3 (m.d 1 5) (by simp) with h4009 | h4009
                                      · linarith only [h3, h4009, hlam]
                                      · linarith only [h3924, h4009, hlam]
                              · linarith only [h4002, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              rcases p3993_3 (m.d 0 1) (by simp) with h4013 | h4013
                              · rcases p3993_3 (m.d 1 2) (by simp) with h4014 | h4014
                                · linarith only [h0, h4014, hlam]
                                · linarith only [h3920, h4014, hlam]
                              · linarith only [h4013, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              rcases p3993_3 (m.d 0 1) (by simp) with h4018 | h4018
                              · rcases p3993_3 (m.d 1 2) (by simp) with h4019 | h4019
                                · linarith only [h0, h4019, hlam]
                                · rcases p3993_3 (m.d 1 3) (by simp) with h4021 | h4021
                                  · linarith only [h1, h4021, hlam]
                                  · rcases p3993_3 (m.d 1 4) (by simp) with h4023 | h4023
                                    · linarith only [h2, h4023, hlam]
                                    · rcases p3993_3 (m.d 1 5) (by simp) with h4025 | h4025
                                      · linarith only [h4025, hlam, p3993_0]
                                      · rcases h2bigk with h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3920, h3987, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h4, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3687, h3987, h3989, hc34, hc45, hlam, hphi, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3687, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h0, hlam, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3918, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3918, h3924, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3993_1, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3921, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          rcases p4027_3 (m.d 0 2) (by simp) with h4038 | h4038
                                          · linarith only [h4038, hlam, p4027_0]
                                          · rcases p4027_3 (m.d 1 2) (by simp) with h4040 | h4040
                                            · linarith only [h3918, h4040, hlam]
                                            · rcases p4027_3 (m.d 2 3) (by simp) with h4042 | h4042
                                              · rcases p4027_3 (m.d 2 4) (by simp) with h4043 | h4043
                                                · linarith only [h3987, h4043, hlam]
                                                · rcases p4027_3 (m.d 2 5) (by simp) with h4045 | h4045
                                                  · linarith only [h3988, h4045, hlam]
                                                  · linarith only [h3687, h4045, hlam]
                                              · linarith only [h4042, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          rcases p4027_3 (m.d 0 2) (by simp) with h4049 | h4049
                                          · linarith only [h4, h4049, hlam]
                                          · linarith only [h0, h4049, hlam]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3918, h3920, h3924, h3988, hlam, p4027_2]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3687, hc02, hc23, hlam, hphi, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3686, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3920, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3987, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3989, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h0, h3920, h3987, h3989, hc34, hc45, hlam, hphi, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3920, h3987, h3989, hc34, hc45, hlam, hphi, p4027_1]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [h3988, hlam, p4027_0]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          rcases p4027_3 (m.d 0 2) (by simp) with h4063 | h4063
                                          · linarith only [h3687, h4063, hlam]
                                          · linarith only [h3686, h4063, hlam]
                                        · have p4027_0 := h4027c.1
                                          have p4027_1 := h4027c.2.1
                                          have p4027_2 := h4027c.2.2.1
                                          have p4027_3 := h4027c.2.2.2
                                          linarith only [hlam, p4027_0]
                              · linarith only [h4018, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h0, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3918, hlam, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h0, h3687, h3920, h3987, h3989, hc34, hc45, hlam, hphi, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3921, hlam, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h1, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3924, h3988, hc12, hc23, hlam, hphi, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3920, h3924, h3987, h3988, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3924, hlam, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h2, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3920, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3923, hlam, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3985, hlam, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3, hlam, p3993_0]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3, h3920, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [h3918, h3920, h3924, h3987, h3988, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3993_1]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              rcases p3993_3 (m.d 0 1) (by simp) with h4086 | h4086
                              · rcases p3993_3 (m.d 1 2) (by simp) with h4087 | h4087
                                · linarith only [h3921, h4087, hlam]
                                · linarith only [h3920, h4087, hlam]
                              · linarith only [h2, h4086, hlam]
                            · have p3993_0 := h3993c.1
                              have p3993_1 := h3993c.2.1
                              have p3993_2 := h3993c.2.2.1
                              have p3993_3 := h3993c.2.2.2
                              linarith only [hlam, p3993_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4092 | h4092
                        · linarith only [h0, h3920, h4092, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4094 | h4094
                          · linarith only [h0, h3920, h3987, h3988, h4, h4092, h4094, hlam]
                          · linarith only [h0, h3920, h3987, h3988, h4, h4094, hc34, hc45, hlam, hphi]
                    · linarith only [h3915, h3987, h4, hlam]
              · linarith only [h3915, h3916, h3918, h3920, h3923, hc24, hc45, hlam, hphi]
          · linarith only [h3686, h3920, h4, hc12, hc23, hlam, hphi]
    · linarith only [h3686, h3915, h4, hlam]

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4101 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h4102 | h4102
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4103 | h4103
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4104 | h4104
      · linarith only [h0, h4, h4104, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4106 | h4106
        · linarith only [h0, h3686, h4106, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4108 | h4108
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4109 | h4109
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4110 | h4110
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4111 | h4111
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4112 | h4112
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4113 | h4113
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4114 | h4114
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4115 | h4115
                        · linarith only [h1, h4109, h4115, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases h1bigk with h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c | h4117c
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4108, hc01, hlam, hphi, ht0b, ht5b, p4117_1, u5ehi2]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4104, h4108, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4106, h4108, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            rcases p4117_3 (m.d 0 1) (by simp) with h4122 | h4122
                            · rcases p4117_3 (m.d 1 2) (by simp) with h4123 | h4123
                              · linarith only [h0, h4123, hlam]
                              · linarith only [h4108, h4123, hlam]
                            · linarith only [h4122, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h0, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4104, hlam, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4106, hlam, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h0, h4108, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h1, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h1, h4108, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h1, h4106, h4108, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h1, h4108, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h2, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4108, h4114, h4115, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4109, hlam, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h1, h4108, h4109, h4114, h4115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4117_1]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h3, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4108, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4110, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [h4111, hlam, p4117_0]
                          · have p4117_0 := h4117c.1
                            have p4117_1 := h4117c.2.1
                            have p4117_2 := h4117c.2.2.1
                            have p4117_3 := h4117c.2.2.2
                            linarith only [hlam, p4117_0]
                      · linarith only [h0, h3686, h4108, h4114, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h0, h4, h4108, h4113, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h4, h4108, h4112, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h4102, h4103, h4106, h4108, h4111, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h4104, h4108, h4110, hlam]
            · linarith only [h4, h4102, h4104, h4108, h4109, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · linarith only [h4, h4101, h4108, hc12, hc23, hlam, hphi]
    · linarith only [h3686, h4101, h4103, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4155 | h4155
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4156 | h4156
      · linarith only [h0, h4, h4156, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4158 | h4158
        · linarith only [h3686, h4101, h4156, h4158, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4160 | h4160
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4161 | h4161
            · linarith only [h1, h4102, h4161, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4163 | h4163
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4164 | h4164
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4165 | h4165
                  · linarith only [h1, h4102, h4156, h4160, h4165, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h4, h4160, h4165, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h4155, h4156, h4160, h4161, h4164, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h4156, h4160, h4163, hlam]
          · linarith only [h4, h4101, h4160, hc12, hc23, hlam, hphi]
    · linarith only [h4, h4101, h4102, h4155, hlam]

end R2N4
