import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S0
import Jsp000404.R1LeavesN7_35S1
import Jsp000404.R1LeavesN7_35S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1980 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2294 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2945 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 3 4 (by decide) (by decide) with h3359 | h3359
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3360 | h3360
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3361 | h3361
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3362 | h3362
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3363 | h3363
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3364 | h3364
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3365 | h3365
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3366 | h3366
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3367 | h3367
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3368 | h3368
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3369 | h3369
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3370 | h3370
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3371 | h3371
                          · linarith only [h3359, h3371, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h3359, h3361, h3371, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h2945, h3359, h3361, h3370, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2294, h3360, h3369, hlam]
                    · linarith only [h2294, h3359, h3368, hlam]
                  · linarith only [h2945, h3361, h3363, h3367, hlam]
                · linarith only [h2294, h3360, h3362, h3366, hlam]
              · linarith only [h2294, h3359, h3362, h3365, hlam]
            · linarith only [h0, h2294, h3362, h3364, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h2294, h3362, h3363, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3382 | h3382
          · linarith only [h0, h2945, h3362, h3382, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3384 | h3384
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3385 | h3385
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3386 | h3386
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3387 | h3387
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3388 | h3388
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3389 | h3389
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3390 | h3390
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3391 | h3391
                          · linarith only [h3359, h3391, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h3359, h3361, h3391, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h3359, h3361, h3382, h3390, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1980, h3360, h3382, h3384, h3388, h3389, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h3359, h3388, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1501, h3361, h3387, hlam]
                · linarith only [h3360, h3386, h811, hlam]
              · linarith only [h3359, h3385, h811, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3400 | h3400
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3401 | h3401
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3402 | h3402
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3403 | h3403
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3404 | h3404
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3405 | h3405
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3406 | h3406
                          · linarith only [h3359, h3406, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h3359, h3361, h3406, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h3359, h3361, h3405, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h3360, h3382, h3403, h3404, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h3362, h3403, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1501, h3361, h3402, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h3360, h3401, h811, hlam]
              · linarith only [h3359, h3400, h811, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3415 | h3415
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3416 | h3416
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3417 | h3417
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3418 | h3418
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3419 | h3419
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3420 | h3420
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3421 | h3421
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3422 | h3422
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3423 | h3423
                        · linarith only [h0, h2945, h3361, h3415, h3421, h3423, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2945, h3418, h3420, h3423, hc01, hc13, hlam, hphi]
                      · linarith only [h3360, h3422, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2294, h3359, h3360, h3421, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3428 | h3428
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3429 | h3429
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3430 | h3430
                        · linarith only [h1501, h3420, h3428, h3430, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3432 | h3432
                          · linarith only [h3359, h3420, h3432, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases h1bigk with h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h0, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h811, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h1501, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h1980, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              rcases p3434_3 (m.d 0 1) (by simp) with h3440 | h3440
                              · linarith only [h3440, hlam, p3434_0]
                              · rcases p3434_3 (m.d 1 2) (by simp) with h3442 | h3442
                                · rcases p3434_3 (m.d 1 3) (by simp) with h3443 | h3443
                                  · linarith only [h3415, h3443, hlam]
                                  · linarith only [h3443, h811, hlam]
                                · linarith only [h3442, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h811, hc01, hc12, hlam, hphi, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h0, h2945, h3416, hc01, hc12, hlam, hphi, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h0, h2945, h3416, h3420, hc01, hc12, hlam, hphi, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              rcases p3434_3 (m.d 0 1) (by simp) with h3451 | h3451
                              · linarith only [h3451, hlam, p3434_0]
                              · rcases p3434_3 (m.d 1 2) (by simp) with h3453 | h3453
                                · rcases p3434_3 (m.d 1 3) (by simp) with h3454 | h3454
                                  · rcases p3434_3 (m.d 1 4) (by simp) with h3455 | h3455
                                    · linarith only [h3418, h3455, hlam]
                                    · linarith only [h1501, h3455, hlam]
                                  · linarith only [h3454, hlam, p3434_0]
                                · linarith only [h0, h3453, hlam]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3415, hlam, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h0, h2945, h3416, hc01, hc13, hlam, hphi, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h0, h2945, h3415, h3416, h3420, hc01, hc12, hlam, hphi, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3420, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3416, hlam, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3418, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3420, hlam, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              rcases p3434_3 (m.d 0 1) (by simp) with h3469 | h3469
                              · linarith only [h3469, hlam, p3434_0]
                              · rcases p3434_3 (m.d 1 2) (by simp) with h3471 | h3471
                                · rcases p3434_3 (m.d 1 3) (by simp) with h3472 | h3472
                                  · rcases p3434_3 (m.d 1 4) (by simp) with h3473 | h3473
                                    · linarith only [h3420, h3473, hlam]
                                    · linarith only [h1501, h3473, hlam]
                                  · linarith only [h3472, h811, hlam]
                                · linarith only [h0, h3471, hlam]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3417, hlam, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h3419, hlam, p3434_0]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [h1501, hc01, hc15, hlam, hphi, p3434_1]
                            · have p3434_0 := h3434c.1
                              have p3434_1 := h3434c.2.1
                              have p3434_2 := h3434c.2.2.1
                              have p3434_3 := h3434c.2.2.2
                              linarith only [hlam, p3434_0]
                      · linarith only [h2294, h3360, h3429, hlam]
                    · linarith only [h2294, h3359, h3360, h3428, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h3360, h3419, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h2294, h3359, h3415, h3418, hlam]
            · linarith only [h0, h2294, h3415, h3417, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h2294, h3415, h3416, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3488 | h3488
          · linarith only [h0, h2945, h3415, h3488, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3490 | h3490
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3491 | h3491
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3492 | h3492
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3493 | h3493
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3494 | h3494
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3495 | h3495
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3496 | h3496
                        · linarith only [h0, h2945, h3361, h3488, h3490, h3494, h3496, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h3488, h3490, h3491, h3493, h3496, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h3360, h3415, h3495, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h2945, h3359, h3361, h3415, h3490, h3493, h3494, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h3488, h3490, h3493, hlam]
                · linarith only [h3360, h3492, h811, hlam]
              · linarith only [h3359, h3360, h3491, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3504 | h3504
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3505 | h3505
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3506 | h3506
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3507 | h3507
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3508 | h3508
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3509 | h3509
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3510 | h3510
                          · linarith only [h3359, h3361, h3510, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases h1bigk with h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h0, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h811, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h1501, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h1980, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3490, h3509, hc01, hc24, hlam, hphi, ht12, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3415, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3488, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3490, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              rcases p3512_3 (m.d 0 1) (by simp) with h3523 | h3523
                              · linarith only [h3523, hlam, p3512_0]
                              · rcases p3512_3 (m.d 1 2) (by simp) with h3525 | h3525
                                · linarith only [h3415, h3525, hlam]
                                · linarith only [h0, h3525, hlam]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h0, h3415, hc01, hc23, hlam, hphi, ht12, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h1501, h3415, hc01, hc23, hlam, hphi, ht12, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h0, h3415, h3490, hc01, hc23, hlam, hphi, ht12, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              rcases p3512_3 (m.d 0 1) (by simp) with h3532 | h3532
                              · linarith only [h3532, hlam, p3512_0]
                              · rcases p3512_3 (m.d 1 2) (by simp) with h3534 | h3534
                                · linarith only [h3488, h3534, hlam]
                                · linarith only [h0, h3534, hlam]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3504, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h0, h2945, h3361, h3488, h3506, h3507, hc01, hc23, hlam, hphi, ht12, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              rcases p3512_3 (m.d 0 1) (by simp) with h3541 | h3541
                              · linarith only [h3541, hlam, p3512_0]
                              · rcases p3512_3 (m.d 1 2) (by simp) with h3543 | h3543
                                · linarith only [h3490, h3543, hlam]
                                · linarith only [h0, h3543, hlam]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p3512_1]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3505, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [h3506, hlam, p3512_0]
                            · have p3512_0 := h3512c.1
                              have p3512_1 := h3512c.2.1
                              have p3512_2 := h3512c.2.2.1
                              have p3512_3 := h3512c.2.2.2
                              linarith only [hlam, p3512_0]
                        · linarith only [h0, h3488, h3509, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3360, h3415, h3508, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h3359, h3361, h3415, h3504, h3506, h3507, hc05, hlam, hphi, ht0b, ht5b, u0elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3553 | h3553
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3554 | h3554
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3555 | h3555
                        · linarith only [h0, h3488, h3506, h3553, h3555, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3488, h3555, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3360, h3554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h3359, h3415, h3553, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3360, h3505, h811, hlam]
              · linarith only [h3359, h3504, h811, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3562 | h3562
      · linarith only [h3359, h3360, h3562, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3564 | h3564
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3565 | h3565
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3566 | h3566
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3567 | h3567
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3568 | h3568
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3569 | h3569
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3570 | h3570
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3571 | h3571
                      · linarith only [h3359, h3360, h3564, h3571, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h2294, h3568, h3571, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h2294, h3359, h3570, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3575 | h3575
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3576 | h3576
                      · linarith only [h3359, h3360, h3564, h3576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h2294, h3564, h3568, h3576, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2294, h3359, h3575, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3580 | h3580
                  · linarith only [h1501, h3562, h3567, h3568, h3580, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3582 | h3582
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3583 | h3583
                      · linarith only [h3568, h3583, h811, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3585 | h3585
                        · linarith only [h3565, h3580, h3585, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3587 | h3587
                          · linarith only [h0, h2945, h3359, h3565, h3580, h3587, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases h1bigk with h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h0, hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h811, hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h1501, hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h1980, hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              rcases p3589_3 (m.d 0 1) (by simp) with h3595 | h3595
                              · linarith only [h3595, hlam, p3589_0]
                              · rcases p3589_3 (m.d 1 2) (by simp) with h3597 | h3597
                                · rcases p3589_3 (m.d 1 3) (by simp) with h3598 | h3598
                                  · linarith only [h3564, h3598, hlam]
                                  · linarith only [h3598, h811, hlam]
                                · linarith only [h3597, hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h0, h2945, h3565, h3567, hc01, hc12, hlam, hphi, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h0, h2945, h3565, hc01, hc12, hlam, hphi, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h1980, hc01, hc12, hlam, hphi, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3568, hc01, hc35, hlam, hphi, ht12, ht23, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3564, hlam, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h0, h2945, h3565, h3568, h3587, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3568, hlam, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3567, h3568, h3587, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3565, hlam, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3567, hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [hlam, p3589_0]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3580, hlam, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              rcases p3589_3 (m.d 0 1) (by simp) with h3616 | h3616
                              · linarith only [h3616, hlam, p3589_0]
                              · rcases p3589_3 (m.d 1 2) (by simp) with h3618 | h3618
                                · rcases p3589_3 (m.d 1 3) (by simp) with h3619 | h3619
                                  · linarith only [h3568, h3619, hlam]
                                  · linarith only [h3619, h811, hlam]
                                · linarith only [h0, h3618, hlam]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h3566, hlam, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h811, hc01, hc15, hlam, hphi, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [h0, h2945, h3565, h3568, h3587, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3589_1]
                            · have p3589_0 := h3589c.1
                              have p3589_1 := h3589c.2.1
                              have p3589_2 := h3589c.2.2.1
                              have p3589_3 := h3589c.2.2.2
                              linarith only [hlam, p3589_0]
                    · linarith only [h2294, h3359, h3582, hlam]
              · linarith only [h3359, h3360, h3567, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
            · linarith only [h0, h2294, h3564, h3566, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h2294, h3564, h3565, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3631 | h3631
          · linarith only [h0, h2945, h3564, h3631, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3633 | h3633
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3634 | h3634
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3635 | h3635
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3636 | h3636
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3637 | h3637
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3638 | h3638
                      · linarith only [h3359, h3360, h3631, h3633, h3637, h3638, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3631, h3633, h3635, h3637, h3638, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h3359, h3360, h3564, h3633, h3635, h3637, hlam]
                  · linarith only [h3359, h3360, h3631, h3633, h3635, h3636, hc34, hc45, hlam, hphi]
                · linarith only [h3631, h3633, h3634, h3635, hlam]
              · linarith only [h3359, h3634, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3645 | h3645
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3646 | h3646
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3647 | h3647
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3648 | h3648
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3649 | h3649
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3650 | h3650
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3651 | h3651
                          · linarith only [h2945, h3359, h3360, h3562, h3564, h3646, h3651, hc02, hc23, hlam, hphi]
                          · rcases h1bigk with h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h0, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h811, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h1501, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h1980, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3633, hc01, hc25, hlam, hphi, ht12, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3564, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3631, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3633, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              rcases p3653_3 (m.d 0 1) (by simp) with h3664 | h3664
                              · linarith only [h3664, hlam, p3653_0]
                              · rcases p3653_3 (m.d 1 2) (by simp) with h3666 | h3666
                                · linarith only [h3564, h3666, hlam]
                                · linarith only [h0, h3666, hlam]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h0, h3564, hc01, hc23, hlam, hphi, ht12, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3360, h3564, h3647, h3651, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h0, h3564, h3633, hc01, hc23, hlam, hphi, ht12, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              rcases p3653_3 (m.d 0 1) (by simp) with h3673 | h3673
                              · linarith only [h3673, hlam, p3653_0]
                              · rcases p3653_3 (m.d 1 2) (by simp) with h3675 | h3675
                                · linarith only [h3631, h3675, hlam]
                                · linarith only [h0, h3675, hlam]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3645, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3359, h3360, h3631, h3647, h3648, h3651, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              rcases p3653_3 (m.d 0 1) (by simp) with h3682 | h3682
                              · linarith only [h3682, hlam, p3653_0]
                              · rcases p3653_3 (m.d 1 2) (by simp) with h3684 | h3684
                                · linarith only [h3633, h3684, hlam]
                                · linarith only [h0, h3684, hlam]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p3653_1]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3646, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [h3647, hlam, p3653_0]
                            · have p3653_0 := h3653c.1
                              have p3653_1 := h3653c.2.1
                              have p3653_2 := h3653c.2.2.1
                              have p3653_3 := h3653c.2.2.2
                              linarith only [hlam, p3653_0]
                        · linarith only [h0, h3631, h3650, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3564, h3646, h3649, hlam]
                    · linarith only [h3359, h3360, h3564, h3646, h3648, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3694 | h3694
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3695 | h3695
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3696 | h3696
                        · linarith only [h1501, h3647, h3696, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h3631, h3696, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3564, h3646, h3695, hlam]
                    · linarith only [h3359, h3360, h3564, h3646, h3694, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3701 | h3701
                  · linarith only [h0, h2945, h3562, h3645, h3646, h3701, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3703 | h3703
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3704 | h3704
                      · linarith only [h3646, h3704, h811, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3564, h3704, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3359, h3564, h3703, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h3359, h3645, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3709 | h3709
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3710 | h3710
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3711 | h3711
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3712 | h3712
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3713 | h3713
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3714 | h3714
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3715 | h3715
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3716 | h3716
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3717 | h3717
                    · linarith only [h3359, h3709, h3711, h3717, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h2294, h3714, h3717, hc01, hc13, hlam, hphi]
                  · linarith only [h3710, h3716, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h3709, h3715, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3722 | h3722
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3723 | h3723
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3724 | h3724
                    · linarith only [h3359, h3709, h3711, h3724, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3726 | h3726
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3727 | h3727
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3728 | h3728
                          · rcases h1bigk with h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c | h3729c
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h0, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h811, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h1501, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h1980, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              rcases p3729_3 (m.d 0 1) (by simp) with h3735 | h3735
                              · linarith only [h3735, hlam, p3729_0]
                              · rcases p3729_3 (m.d 1 2) (by simp) with h3737 | h3737
                                · rcases p3729_3 (m.d 1 3) (by simp) with h3738 | h3738
                                  · linarith only [h3711, h3738, hlam]
                                  · linarith only [h3738, h811, hlam]
                                · linarith only [h3737, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h811, hc01, hc12, hlam, hphi, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h0, h2294, h3711, h3714, hc01, hc12, hlam, hphi, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h1980, hc01, hc12, hlam, hphi, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3714, hc01, hc34, hlam, hphi, ht12, ht23, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3711, hlam, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3714, hlam, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h1980, h3714, hc01, hc34, hlam, hphi, ht12, ht23, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              rcases p3729_3 (m.d 0 1) (by simp) with h3751 | h3751
                              · linarith only [h3751, hlam, p3729_0]
                              · rcases p3729_3 (m.d 1 2) (by simp) with h3753 | h3753
                                · rcases p3729_3 (m.d 1 3) (by simp) with h3754 | h3754
                                  · linarith only [h3714, h3754, hlam]
                                  · linarith only [h3754, h811, hlam]
                                · linarith only [h0, h3753, hlam]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3712, hlam, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h811, hc01, hc14, hlam, hphi, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h1980, h3714, hc01, hc34, hlam, hphi, ht12, ht23, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3714, h3722, hc01, hc34, hlam, hphi, ht12, ht23, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3713, hlam, p3729_1]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3722, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [h3723, hlam, p3729_0]
                            · have p3729_0 := h3729c.1
                              have p3729_1 := h3729c.2.1
                              have p3729_2 := h3729c.2.2.1
                              have p3729_3 := h3729c.2.2.2
                              linarith only [hlam, p3729_0]
                          · linarith only [h3714, h3728, h811, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h2294, h3710, h3724, h3727, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h2294, h3709, h3726, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1501, h3710, h3723, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h2294, h3709, h3711, h3722, hlam]
            · linarith only [h0, h2294, h3711, h3713, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h2294, h3711, h3712, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3774 | h3774
          · linarith only [h0, h2945, h3711, h3774, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3776 | h3776
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3777 | h3777
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3778 | h3778
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3779 | h3779
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3780 | h3780
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3781 | h3781
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3782 | h3782
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3783 | h3783
                          · rcases h1bigk with h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c | h3784c
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h0, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h811, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1501, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1980, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3774, h3780, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3711, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3774, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1980, h3774, h3780, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              rcases p3784_3 (m.d 0 1) (by simp) with h3795 | h3795
                              · linarith only [h3795, hlam, p3784_0]
                              · rcases p3784_3 (m.d 1 2) (by simp) with h3797 | h3797
                                · linarith only [h3711, h3797, hlam]
                                · linarith only [h0, h3797, hlam]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h0, h3711, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1501, h3711, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1980, h3711, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              rcases p3784_3 (m.d 0 1) (by simp) with h3804 | h3804
                              · linarith only [h3804, hlam, p3784_0]
                              · rcases p3784_3 (m.d 1 2) (by simp) with h3806 | h3806
                                · linarith only [h3774, h3806, hlam]
                                · linarith only [h0, h3806, hlam]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1980, h3776, hc01, hc14, hlam, hphi, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3777, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h1980, h3774, h3780, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3711, h3776, hc01, hc23, hlam, hphi, ht12, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3776, hlam, p3784_1]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3778, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [h3779, hlam, p3784_0]
                            · have p3784_0 := h3784c.1
                              have p3784_1 := h3784c.2.1
                              have p3784_2 := h3784c.2.2.1
                              have p3784_3 := h3784c.2.2.2
                              linarith only [hlam, p3784_0]
                          · linarith only [h3359, h3710, h3783, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h3710, h3774, h3782, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h3709, h3711, h3781, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h3711, h3777, h3780, hlam]
                  · linarith only [h3710, h3779, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h3359, h3709, h3777, h3778, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3824 | h3824
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3825 | h3825
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3826 | h3826
                    · linarith only [h3777, h3826, h811, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1980, h3711, h3776, h3826, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3710, h3825, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h1980, h3709, h3711, h3776, h3824, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3831 | h3831
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3832 | h3832
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3833 | h3833
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3834 | h3834
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3835 | h3835
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3836 | h3836
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3837 | h3837
                          · rcases h1bigk with h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c | h3838c
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h811, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h1501, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h1980, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3776, h3836, hc01, hc24, hlam, hphi, ht12, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3711, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3774, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3776, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              rcases p3838_3 (m.d 0 1) (by simp) with h3849 | h3849
                              · linarith only [h3849, hlam, p3838_0]
                              · rcases p3838_3 (m.d 1 2) (by simp) with h3851 | h3851
                                · linarith only [h3711, h3851, hlam]
                                · linarith only [h0, h3851, hlam]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, h3711, hc01, hc23, hlam, hphi, ht12, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, h3711, h3776, h3833, hc01, hc23, hlam, hphi, ht12, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, h3711, h3776, hc01, hc23, hlam, hphi, ht12, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              rcases p3838_3 (m.d 0 1) (by simp) with h3858 | h3858
                              · linarith only [h3858, hlam, p3838_0]
                              · rcases p3838_3 (m.d 1 2) (by simp) with h3860 | h3860
                                · linarith only [h3774, h3860, hlam]
                                · linarith only [h0, h3860, hlam]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3831, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, h3774, h3776, h3834, hc01, hc23, hlam, hphi, ht12, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              rcases p3838_3 (m.d 0 1) (by simp) with h3867 | h3867
                              · linarith only [h3867, hlam, p3838_0]
                              · rcases p3838_3 (m.d 1 2) (by simp) with h3869 | h3869
                                · linarith only [h3776, h3869, hlam]
                                · linarith only [h0, h3869, hlam]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p3838_1]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3832, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [h3833, hlam, p3838_0]
                            · have p3838_0 := h3838c.1
                              have p3838_1 := h3838c.2.1
                              have p3838_2 := h3838c.2.2.1
                              have p3838_3 := h3838c.2.2.2
                              linarith only [hlam, p3838_0]
                          · linarith only [h3359, h3710, h3837, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h3710, h3774, h3836, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h3359, h3709, h3711, h3831, h3835, hlam]
                    · linarith only [h3711, h3831, h3834, hlam]
                  · linarith only [h3359, h3709, h3710, h3831, h3833, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h3359, h3709, h3831, h3832, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3882 | h3882
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3883 | h3883
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3884 | h3884
                    · linarith only [h3831, h3884, h811, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3711, h3884, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3710, h3883, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h3709, h3882, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
      · linarith only [h3359, h3709, h3710, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3890 | h3890
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3891 | h3891
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3892 | h3892
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3893 | h3893
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3894 | h3894
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3895 | h3895
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3896 | h3896
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3897 | h3897
                    · linarith only [h3359, h3891, h3897, h811, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2294, h3894, h3897, hc01, hc13, hlam, hphi]
                  · linarith only [h3890, h3896, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h2294, h3359, h3894, h3895, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3902 | h3902
                · linarith only [h0, h2294, h3709, h3894, h3902, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3904 | h3904
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3905 | h3905
                    · linarith only [h3894, h3905, h811, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3907 | h3907
                      · linarith only [h3891, h3902, h3907, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3909 | h3909
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3910 | h3910
                          · rcases h1bigk with h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c | h3911c
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h0, hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h811, hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h1501, hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h1980, hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              rcases p3911_3 (m.d 0 1) (by simp) with h3917 | h3917
                              · linarith only [h3917, hlam, p3911_0]
                              · rcases p3911_3 (m.d 1 2) (by simp) with h3919 | h3919
                                · rcases p3911_3 (m.d 1 3) (by simp) with h3920 | h3920
                                  · linarith only [h3891, h3920, hlam]
                                  · linarith only [h3920, h811, hlam]
                                · linarith only [h3919, hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h0, h2294, h3891, hc01, hc12, hlam, hphi, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h1501, hc01, hc12, hlam, hphi, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h0, h2294, h3891, h3902, hc01, hc12, hlam, hphi, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3902, h3910, hc01, hc34, hlam, hphi, ht12, ht23, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3891, hlam, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3894, hlam, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3902, hlam, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              rcases p3911_3 (m.d 0 1) (by simp) with h3933 | h3933
                              · linarith only [h3933, hlam, p3911_0]
                              · rcases p3911_3 (m.d 1 2) (by simp) with h3935 | h3935
                                · rcases p3911_3 (m.d 1 3) (by simp) with h3936 | h3936
                                  · linarith only [h3894, h3936, hlam]
                                  · linarith only [h3936, h811, hlam]
                                · linarith only [h0, h3935, hlam]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3892, hlam, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h0, h2294, h3891, hc01, hc14, hlam, hphi, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h0, h2294, h3891, h3902, hc01, hc14, hlam, hphi, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              rcases p3911_3 (m.d 0 1) (by simp) with h3944 | h3944
                              · linarith only [h3944, hlam, p3911_0]
                              · rcases p3911_3 (m.d 1 2) (by simp) with h3946 | h3946
                                · rcases p3911_3 (m.d 1 3) (by simp) with h3947 | h3947
                                  · linarith only [h3902, h3947, hlam]
                                  · linarith only [h3947, h811, hlam]
                                · linarith only [h0, h3946, hlam]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3893, hlam, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h0, h2294, h3891, hc01, hc15, hlam, hphi, p3911_1]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [h3904, hlam, p3911_0]
                            · have p3911_0 := h3911c.1
                              have p3911_1 := h3911c.2.1
                              have p3911_2 := h3911c.2.2.1
                              have p3911_3 := h3911c.2.2.2
                              linarith only [hlam, p3911_0]
                          · linarith only [h3890, h3894, h3910, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h2945, h3890, h3909, hlam]
                  · linarith only [h3890, h3904, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
            · linarith only [h0, h2294, h3891, h3893, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h2294, h3891, h3892, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3960 | h3960
          · linarith only [h0, h2945, h3891, h3960, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3962 | h3962
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3963 | h3963
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3964 | h3964
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3965 | h3965
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3966 | h3966
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3967 | h3967
                      · linarith only [h0, h2294, h3709, h3960, h3962, h3967, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h3960, h3966, h3967, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h2294, h3709, h3891, h3962, h3963, h3964, h3966, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h2294, h3709, h3890, h3960, h3962, h3964, h3965, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h2294, h3359, h3963, h3964, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3973 | h3973
                · linarith only [h0, h2294, h3709, h3963, h3973, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3891, h3962, h3973, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3976 | h3976
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3977 | h3977
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3978 | h3978
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3979 | h3979
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3980 | h3980
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3981 | h3981
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3982 | h3982
                          · rcases h1bigk with h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h811, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h1501, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h1980, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3962, h3981, hc01, hc24, hlam, hphi, ht12, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3891, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3960, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3962, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              rcases p3983_3 (m.d 0 1) (by simp) with h3994 | h3994
                              · linarith only [h3994, hlam, p3983_0]
                              · rcases p3983_3 (m.d 1 2) (by simp) with h3996 | h3996
                                · linarith only [h3891, h3996, hlam]
                                · linarith only [h0, h3996, hlam]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, h2294, h3709, h3891, h3977, h3978, hc01, hc23, hlam, hphi, ht12, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, h2294, h3709, h3891, h3977, hc01, hc23, hlam, hphi, ht12, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              rcases p3983_3 (m.d 0 1) (by simp) with h4003 | h4003
                              · linarith only [h4003, hlam, p3983_0]
                              · rcases p3983_3 (m.d 1 2) (by simp) with h4005 | h4005
                                · linarith only [h3960, h4005, hlam]
                                · linarith only [h0, h4005, hlam]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3976, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, h2294, h3709, h3960, h3977, h3979, hc01, hc23, hlam, hphi, ht12, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              rcases p3983_3 (m.d 0 1) (by simp) with h4012 | h4012
                              · linarith only [h4012, hlam, p3983_0]
                              · rcases p3983_3 (m.d 1 2) (by simp) with h4014 | h4014
                                · linarith only [h3962, h4014, hlam]
                                · linarith only [h0, h4014, hlam]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p3983_1]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3977, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [h3978, hlam, p3983_0]
                            · have p3983_0 := h3983c.1
                              have p3983_1 := h3983c.2.1
                              have p3983_2 := h3983c.2.2.1
                              have p3983_3 := h3983c.2.2.2
                              linarith only [hlam, p3983_0]
                          · linarith only [h3890, h3982, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h3890, h3960, h3981, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h3891, h3980, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h3891, h3976, h3979, hlam]
                  · linarith only [h3359, h3890, h3976, h3978, hlam]
                · linarith only [h0, h2294, h3359, h3976, h3977, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4027 | h4027
                · linarith only [h0, h2294, h3709, h3976, h4027, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4029 | h4029
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4030 | h4030
                    · linarith only [h3976, h4030, h811, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3891, h4030, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3890, h4029, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4034 | h4034
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4035 | h4035
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4036 | h4036
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4037 | h4037
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4038 | h4038
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4039 | h4039
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4040 | h4040
                    · linarith only [h0, h2294, h3359, h4034, h4040, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2294, h4034, h4037, h4040, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4043 | h4043
                    · linarith only [h0, h2294, h3359, h4034, h4043, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2294, h4037, h4039, h4043, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h2294, h3359, h4037, h4038, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4047 | h4047
                · linarith only [h0, h2294, h3709, h4037, h4047, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4049 | h4049
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4050 | h4050
                    · linarith only [h4037, h4050, h811, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4052 | h4052
                      · linarith only [h4034, h4047, h4052, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4054 | h4054
                        · linarith only [h0, h2294, h3359, h3890, h4035, h4054, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2945, h4049, h4054, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4057 | h4057
                    · linarith only [h0, h2294, h3359, h4034, h4047, h4057, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4059 | h4059
                      · linarith only [h4034, h4047, h4059, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4061 | h4061
                        · linarith only [h4037, h4049, h4061, h811, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4063 | h4063
                          · linarith only [h0, h2294, h4034, h4037, h4049, h4063, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h2294, h4034, h4037, h4063, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h2294, h4034, h4036, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h2294, h4034, h4035, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4068 | h4068
          · linarith only [h0, h2945, h4034, h4068, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4070 | h4070
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4071 | h4071
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4072 | h4072
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4073 | h4073
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4074 | h4074
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4075 | h4075
                      · linarith only [h0, h2294, h3709, h4068, h4070, h4074, h4075, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4068, h4074, h4075, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h4034, h4071, h4074, hlam]
                  · linarith only [h4068, h4070, h4073, hlam]
                · linarith only [h0, h2294, h3359, h4071, h4072, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4081 | h4081
                · linarith only [h0, h2294, h3709, h4071, h4081, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h4034, h4070, h4081, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4084 | h4084
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4085 | h4085
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4086 | h4086
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4087 | h4087
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4088 | h4088
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4089 | h4089
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4090 | h4090
                          · linarith only [h0, h2294, h3359, h3890, h4084, h4090, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h2294, h3359, h4086, h4090, hc01, hc14, hlam, hphi]
                        · linarith only [h0, h2945, h4034, h4084, h4086, h4089, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h4034, h4085, h4088, hlam]
                    · linarith only [h0, h2294, h3709, h4034, h4085, h4087, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4096 | h4096
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4097 | h4097
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4098 | h4098
                        · linarith only [h0, h4068, h4086, h4096, h4098, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4068, h4098, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h4034, h4097, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h4034, h4084, h4096, hlam]
                · linarith only [h0, h2294, h3359, h4084, h4085, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4104 | h4104
                · linarith only [h0, h2294, h3709, h4084, h4104, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4106 | h4106
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4107 | h4107
                    · linarith only [h4084, h4107, h811, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h4034, h4107, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4110 | h4110
                    · linarith only [h0, h4034, h4084, h4110, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h4034, h4110, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1980 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2294 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 2 4 (by decide) (by decide) with h2945 | h2945
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg811 h1501 h1980 h2294 h2945
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg811 h1501 h1980 h2294 h2945

set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1980 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 2 3 (by decide) (by decide) with h2294 | h2294
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg811 h1501 h1980 h2294
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg811 h1501 h1980 h2294

set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 1 5 (by decide) (by decide) with h1980 | h1980
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg811 h1501 h1980
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg811 h1501 h1980

set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 1 4 (by decide) (by decide) with h1501 | h1501
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x0 m hb0 hb1 hb3 hb4 hg0 hg811 h1501
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1 m hb0 hb1 hb3 hb4 hg0 hg811 h1501

end R2N4
