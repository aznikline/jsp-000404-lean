import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2860 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2861 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2862 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h3393 | h3393
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3394 | h3394
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3395 | h3395
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3396 | h3396
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3397 | h3397
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3398 | h3398
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3399 | h3399
              · linarith only [h2859, h2862, h3399, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3401 | h3401
                · linarith only [h3398, h3399, h3401, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3403 | h3403
                  · linarith only [h3398, h3399, h3401, h3403, hlam]
                  · linarith only [h2858, h2859, h2862, h3397, h3398, h3403, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3406 | h3406
              · linarith only [h2859, h2862, h3406, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3408 | h3408
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3409 | h3409
                  · rcases h2bigk with h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h0, hlam, p3410_1]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      rcases p3410_3 (m.d 0 2) (by simp) with h3413 | h3413
                      · rcases p3410_3 (m.d 1 2) (by simp) with h3414 | h3414
                        · rcases p3410_3 (m.d 2 3) (by simp) with h3415 | h3415
                          · linarith only [h3415, hlam, p3410_0]
                          · rcases p3410_3 (m.d 2 4) (by simp) with h3417 | h3417
                            · linarith only [h2860, h3417, hlam]
                            · linarith only [h3398, h3417, hlam]
                        · linarith only [h3394, h3414, hlam]
                      · linarith only [h3413, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3408, hc45, hlam, hphi, ht0b, ht5b, p3410_1, u0elo1]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      rcases p3410_3 (m.d 0 2) (by simp) with h3423 | h3423
                      · rcases p3410_3 (m.d 1 2) (by simp) with h3424 | h3424
                        · rcases p3410_3 (m.d 2 3) (by simp) with h3425 | h3425
                          · linarith only [h2859, h3425, hlam]
                          · rcases p3410_3 (m.d 2 4) (by simp) with h3427 | h3427
                            · linarith only [h2860, h3427, hlam]
                            · linarith only [h3408, h3427, hlam]
                        · linarith only [h3396, h3424, hlam]
                      · linarith only [h3423, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2860, h3408, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      rcases p3410_3 (m.d 0 2) (by simp) with h3434 | h3434
                      · linarith only [h0, h3434, hlam]
                      · linarith only [h2859, h3434, hlam]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      rcases p3410_3 (m.d 0 2) (by simp) with h3437 | h3437
                      · linarith only [h0, h3437, hlam]
                      · linarith only [h2860, h3437, hlam]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      rcases p3410_3 (m.d 0 2) (by simp) with h3440 | h3440
                      · linarith only [h0, h3440, hlam]
                      · linarith only [h2861, h3440, hlam]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2859, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3394, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3398, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3406, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2860, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3395, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3410_1, u0elo1]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2860, h3406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3410_1, u0elo1]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2861, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3396, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h2861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3410_1, u0elo1]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [h3408, hlam, p3410_0]
                    · have p3410_0 := h3410c.1
                      have p3410_1 := h3410c.2.1
                      have p3410_2 := h3410c.2.2.1
                      have p3410_3 := h3410c.2.2.2
                      linarith only [hlam, p3410_0]
                  · linarith only [h2860, h3393, h3398, h3409, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3459 | h3459
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
                      linarith only [h0, hlam, p3460_1]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      rcases p3460_3 (m.d 0 2) (by simp) with h3463 | h3463
                      · rcases p3460_3 (m.d 1 2) (by simp) with h3464 | h3464
                        · rcases p3460_3 (m.d 2 3) (by simp) with h3465 | h3465
                          · linarith only [h3465, hlam, p3460_0]
                          · rcases p3460_3 (m.d 2 4) (by simp) with h3467 | h3467
                            · linarith only [h2860, h3467, hlam]
                            · linarith only [h3398, h3467, hlam]
                        · linarith only [h3394, h3464, hlam]
                      · linarith only [h3463, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      rcases p3460_3 (m.d 0 2) (by simp) with h3472 | h3472
                      · rcases p3460_3 (m.d 1 2) (by simp) with h3473 | h3473
                        · rcases p3460_3 (m.d 2 3) (by simp) with h3474 | h3474
                          · linarith only [h2859, h3474, hlam]
                          · rcases p3460_3 (m.d 2 4) (by simp) with h3476 | h3476
                            · linarith only [h3476, hlam, p3460_0]
                            · rcases p3460_3 (m.d 2 5) (by simp) with h3478 | h3478
                              · linarith only [h2861, h3478, hlam]
                              · linarith only [h3408, h3478, hlam]
                        · linarith only [h3395, h3473, hlam]
                      · linarith only [h3472, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      rcases p3460_3 (m.d 0 2) (by simp) with h3483 | h3483
                      · rcases p3460_3 (m.d 1 2) (by simp) with h3484 | h3484
                        · rcases p3460_3 (m.d 2 3) (by simp) with h3485 | h3485
                          · linarith only [h2859, h3485, hlam]
                          · rcases p3460_3 (m.d 2 4) (by simp) with h3487 | h3487
                            · linarith only [h2860, h3487, hlam]
                            · rcases p3460_3 (m.d 2 5) (by simp) with h3489 | h3489
                              · linarith only [h3489, hlam, p3460_0]
                              · rcases h5bigk with h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c | h3491c
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p3491_1, u0elo4]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h2862, hlam, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h0, h2858, h3408, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h2858, hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h0, h2858, h2862, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3398, h3408, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h2861, hlam, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3396, hlam, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3406, hlam, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3408, hlam, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3393, h3398, h3408, h3459, hc23, hc34, hlam, hphi, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3397, h3398, h3408, h3459, hc23, hc34, hlam, hphi, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3398, h3408, h3459, hc23, hc34, hlam, hphi, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3398, h3408, h3459, hc23, hc34, hlam, hphi, p3491_1]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3393, hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3397, hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h2858, h3397, h3398, h3408, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3491_1, u0elo4]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [h3459, hlam, p3491_0]
                                · have p3491_0 := h3491c.1
                                  have p3491_1 := h3491c.2.1
                                  have p3491_2 := h3491c.2.2.1
                                  have p3491_3 := h3491c.2.2.2
                                  linarith only [hlam, p3491_0]
                        · linarith only [h3396, h3484, hlam]
                      · linarith only [h3483, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h0, h2858, h3397, h3398, h3408, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3460_1]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h0, h2858, h3397, h3398, h3408, hlam, p3460_2]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h0, h2858, h3397, h3408, hlam, p3460_2]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      rcases p3460_3 (m.d 0 2) (by simp) with h3523 | h3523
                      · linarith only [h0, h3523, hlam]
                      · linarith only [h2861, h3523, hlam]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h2859, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h3394, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h3398, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h3406, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h2860, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h3395, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h0, h2858, h3397, h3408, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3460_1, u0elo1]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h3408, hlam, p3460_1]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h2861, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h3396, hlam, p3460_0]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h2861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3460_1, u0elo1]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [h0, h2858, h3397, h3408, hc24, hlam, hphi, ht0b, ht45, ht5b, p3460_1, u0elo1]
                    · have p3460_0 := h3460c.1
                      have p3460_1 := h3460c.2.1
                      have p3460_2 := h3460c.2.2.1
                      have p3460_3 := h3460c.2.2.2
                      linarith only [hlam, p3460_0]
                  · linarith only [h0, h2858, h3397, h3398, h3459, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3542 | h3542
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3543 | h3543
              · linarith only [h2859, h2862, h3543, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3545 | h3545
                · linarith only [h2860, h3397, h3545, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3547 | h3547
                  · linarith only [h2859, h3397, h3542, h3547, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h2859, h2860, h2862, h3393, h3542, h3547, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3550 | h3550
              · linarith only [h2862, h3393, h3395, h3397, h3542, h3550, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3552 | h3552
                · linarith only [h3395, h3397, h3552, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3554 | h3554
                  · rcases h2bigk with h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c | h3555c
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h0, hlam, p3555_1]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      rcases p3555_3 (m.d 0 2) (by simp) with h3558 | h3558
                      · rcases p3555_3 (m.d 1 2) (by simp) with h3559 | h3559
                        · rcases p3555_3 (m.d 2 3) (by simp) with h3560 | h3560
                          · linarith only [h3560, hlam, p3555_0]
                          · rcases p3555_3 (m.d 2 4) (by simp) with h3562 | h3562
                            · linarith only [h2860, h3562, hlam]
                            · linarith only [h3542, h3562, hlam]
                        · linarith only [h3394, h3559, hlam]
                      · linarith only [h3558, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      rcases p3555_3 (m.d 0 2) (by simp) with h3567 | h3567
                      · rcases p3555_3 (m.d 1 2) (by simp) with h3568 | h3568
                        · rcases p3555_3 (m.d 2 3) (by simp) with h3569 | h3569
                          · linarith only [h2859, h3569, hlam]
                          · rcases p3555_3 (m.d 2 4) (by simp) with h3571 | h3571
                            · linarith only [h3571, hlam, p3555_0]
                            · rcases p3555_3 (m.d 2 5) (by simp) with h3573 | h3573
                              · linarith only [h2861, h3573, hlam]
                              · linarith only [h3552, h3573, hlam]
                        · linarith only [h3395, h3568, hlam]
                      · linarith only [h3567, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      rcases p3555_3 (m.d 0 2) (by simp) with h3578 | h3578
                      · rcases p3555_3 (m.d 1 2) (by simp) with h3579 | h3579
                        · rcases p3555_3 (m.d 2 3) (by simp) with h3580 | h3580
                          · linarith only [h2859, h3580, hlam]
                          · rcases p3555_3 (m.d 2 4) (by simp) with h3582 | h3582
                            · linarith only [h2860, h3582, hlam]
                            · rcases p3555_3 (m.d 2 5) (by simp) with h3584 | h3584
                              · linarith only [h3584, hlam, p3555_0]
                              · rcases h5bigk with h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c | h3586c
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p3586_1, u0elo4]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h2862, hlam, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h0, h2858, h3397, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h2858, hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h0, h2858, h2862, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3397, hlam, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h2861, hlam, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3396, hlam, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3550, hlam, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3552, hlam, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h2861, h3542, h3552, hc23, hc35, hlam, hphi, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3396, h3542, h3552, h3554, hc23, hc34, hlam, hphi, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3542, h3552, h3554, hc23, hc34, hlam, hphi, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3395, h3397, h3542, h3554, hc23, hc34, hlam, hphi, p3586_1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3393, hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3393, h3396, h3542, h3552, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3586_1, u0elo4]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h2860, h3393, h3542, h3552, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3586_1, u0elo1]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [h3554, hlam, p3586_0]
                                · have p3586_0 := h3586c.1
                                  have p3586_1 := h3586c.2.1
                                  have p3586_2 := h3586c.2.2.1
                                  have p3586_3 := h3586c.2.2.2
                                  linarith only [hlam, p3586_0]
                        · linarith only [h3396, h3579, hlam]
                      · linarith only [h3578, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h2860, h3393, h3395, h3397, h3542, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3555_1]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      rcases p3555_3 (m.d 0 2) (by simp) with h3616 | h3616
                      · linarith only [h0, h3616, hlam]
                      · linarith only [h2859, h3616, hlam]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      rcases p3555_3 (m.d 0 2) (by simp) with h3619 | h3619
                      · linarith only [h0, h3619, hlam]
                      · linarith only [h2860, h3619, hlam]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      rcases p3555_3 (m.d 0 2) (by simp) with h3622 | h3622
                      · linarith only [h0, h3622, hlam]
                      · linarith only [h2861, h3622, hlam]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h2859, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h3394, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h3542, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h3550, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h2860, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h3395, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h2858, h3393, h3395, h3397, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3555_1, u0elo0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h3552, hlam, p3555_1]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h2861, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h3396, hlam, p3555_0]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h0, h2858, h3396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3555_1]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [h2860, h3393, h3396, h3397, hc24, hlam, hphi, ht0b, ht45, ht5b, p3555_1, u0elo1]
                    · have p3555_0 := h3555c.1
                      have p3555_1 := h3555c.2.1
                      have p3555_2 := h3555c.2.2.1
                      have p3555_3 := h3555c.2.2.2
                      linarith only [hlam, p3555_0]
                  · linarith only [h2860, h3393, h3542, h3554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h2861, h3396, hlam]
      · linarith only [h0, h2860, h3395, hlam]
    · linarith only [h0, h2858, h2859, h3394, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3644 | h3644
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3645 | h3645
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3646 | h3646
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3647 | h3647
          · linarith only [h2858, h3393, h3647, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3649 | h3649
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3650 | h3650
              · linarith only [h2859, h2862, h3650, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3652 | h3652
                · linarith only [h2860, h3647, h3652, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3654 | h3654
                  · linarith only [h2858, h3393, h3646, h3649, h3650, h3654, hlam]
                  · rcases h2bigk with h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c | h3656c
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h0, hlam, p3656_1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3649, hc34, hlam, hphi, ht0b, ht45, ht5b, p3656_1, u0elo1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      rcases p3656_3 (m.d 0 2) (by simp) with h3660 | h3660
                      · rcases p3656_3 (m.d 1 2) (by simp) with h3661 | h3661
                        · rcases p3656_3 (m.d 2 3) (by simp) with h3662 | h3662
                          · linarith only [h2859, h3662, hlam]
                          · linarith only [h3649, h3662, hlam]
                        · linarith only [h3645, h3661, hlam]
                      · linarith only [h3660, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3649, h3650, hc34, hlam, hphi, ht0b, ht45, ht5b, p3656_1, u0elo1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h0, h2858, h3646, h3649, h3650, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3656_1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      rcases p3656_3 (m.d 0 2) (by simp) with h3670 | h3670
                      · linarith only [h0, h3670, hlam]
                      · linarith only [h2859, h3670, hlam]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      rcases p3656_3 (m.d 0 2) (by simp) with h3673 | h3673
                      · linarith only [h0, h3673, hlam]
                      · linarith only [h2860, h3673, hlam]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      rcases p3656_3 (m.d 0 2) (by simp) with h3676 | h3676
                      · linarith only [h0, h3676, hlam]
                      · linarith only [h2861, h3676, hlam]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h2859, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3644, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h2858, h3646, h3650, hc24, hlam, hphi, ht0b, ht45, ht5b, p3656_1, u0elo0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3650, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h2860, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3645, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3649, hlam, p3656_1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3652, hlam, p3656_1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h2861, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h3646, hlam, p3656_0]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h0, h2858, h3646, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3656_1, u0elo1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [h0, h2858, h3646, h3649, hc34, hlam, hphi, ht0b, ht45, ht5b, p3656_1, u0elo1]
                    · have p3656_0 := h3656c.1
                      have p3656_1 := h3656c.2.1
                      have p3656_2 := h3656c.2.2.1
                      have p3656_3 := h3656c.2.2.2
                      linarith only [hlam, p3656_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3694 | h3694
              · linarith only [h2859, h2862, h3694, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3696 | h3696
                · linarith only [h2860, h3393, h3696, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3698 | h3698
                  · rcases h2bigk with h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h0, hlam, p3699_1]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3702 | h3702
                      · rcases p3699_3 (m.d 1 2) (by simp) with h3703 | h3703
                        · rcases p3699_3 (m.d 2 3) (by simp) with h3704 | h3704
                          · linarith only [h3704, hlam, p3699_0]
                          · rcases p3699_3 (m.d 2 4) (by simp) with h3706 | h3706
                            · linarith only [h2860, h3706, hlam]
                            · linarith only [h3649, h3706, hlam]
                        · linarith only [h3644, h3703, hlam]
                      · linarith only [h3702, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3711 | h3711
                      · rcases p3699_3 (m.d 1 2) (by simp) with h3712 | h3712
                        · rcases p3699_3 (m.d 2 3) (by simp) with h3713 | h3713
                          · linarith only [h2859, h3713, hlam]
                          · rcases p3699_3 (m.d 2 4) (by simp) with h3715 | h3715
                            · linarith only [h3715, hlam, p3699_0]
                            · rcases p3699_3 (m.d 2 5) (by simp) with h3717 | h3717
                              · linarith only [h2861, h3717, hlam]
                              · linarith only [h3696, h3717, hlam]
                        · linarith only [h3645, h3712, hlam]
                      · linarith only [h3711, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3722 | h3722
                      · rcases p3699_3 (m.d 1 2) (by simp) with h3723 | h3723
                        · rcases p3699_3 (m.d 2 3) (by simp) with h3724 | h3724
                          · linarith only [h2859, h3724, hlam]
                          · rcases p3699_3 (m.d 2 4) (by simp) with h3726 | h3726
                            · linarith only [h2860, h3726, hlam]
                            · rcases p3699_3 (m.d 2 5) (by simp) with h3728 | h3728
                              · linarith only [h3728, hlam, p3699_0]
                              · rcases h5bigk with h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [hlam, p3730_0]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p3730_1, u0elo4]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h0, h2858, h3649, h3696, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3730_1, u0elo1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h2862, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3393, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h2858, hlam, p3730_0]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [hlam, p3730_0]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h0, h2858, h3649, h3696, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3730_1, u0elo1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h0, h2858, h3393, h3698, hc04, hlam, hphi, ht0b, ht45, ht5b, p3730_1, u0elo1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3647, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h2861, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3646, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [hlam, p3730_0]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3694, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3696, hlam, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h2861, h3649, h3696, hc23, hc35, hlam, hphi, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3646, h3649, h3696, h3698, hc23, hc34, hlam, hphi, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3649, h3696, h3698, hc23, hc34, hlam, hphi, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [hlam, p3730_0]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h2860, h3393, h3649, h3698, hc23, hc34, hlam, hphi, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h2858, h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3730_1]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [h3698, hlam, p3730_0]
                                · have p3730_0 := h3730c.1
                                  have p3730_1 := h3730c.2.1
                                  have p3730_2 := h3730c.2.2.1
                                  have p3730_3 := h3730c.2.2.2
                                  linarith only [hlam, p3730_0]
                        · linarith only [h3646, h3723, hlam]
                      · linarith only [h3722, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3758 | h3758
                      · linarith only [h0, h3758, hlam]
                      · rcases p3699_3 (m.d 1 2) (by simp) with h3760 | h3760
                        · rcases p3699_3 (m.d 2 3) (by simp) with h3761 | h3761
                          · linarith only [h3644, h3761, hlam]
                          · rcases p3699_3 (m.d 2 4) (by simp) with h3763 | h3763
                            · linarith only [h3645, h3763, hlam]
                            · rcases p3699_3 (m.d 2 5) (by simp) with h3765 | h3765
                              · linarith only [h3646, h3765, hlam]
                              · rcases h5bigk with h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c | h3767c
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [hlam, p3767_0]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3767_1, u0elo4]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h0, h2858, h3649, h3696, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3699_1, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h2862, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3393, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h2858, hlam, p3767_0]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [hlam, p3767_0]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h0, h2858, h3649, h3696, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3699_1, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h0, h2858, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3699_1, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3647, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h2861, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3646, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [hlam, p3767_0]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3694, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3696, hlam, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h2861, h3649, h3696, hc23, hc35, hlam, hphi, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3646, h3649, h3696, h3698, hc23, hc34, hlam, hphi, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3649, h3696, h3698, hc23, hc34, hlam, hphi, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [hlam, p3767_0]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h2860, h3393, h3649, h3698, hc23, hc34, hlam, hphi, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h2858, h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3767_1]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [h3698, hlam, p3767_0]
                                · have p3767_0 := h3767c.1
                                  have p3767_1 := h3767c.2.1
                                  have p3767_2 := h3767c.2.2.1
                                  have p3767_3 := h3767c.2.2.2
                                  linarith only [hlam, p3767_0]
                        · linarith only [h0, h3760, hlam]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3795 | h3795
                      · linarith only [h0, h3795, hlam]
                      · linarith only [h2859, h3795, hlam]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3798 | h3798
                      · linarith only [h0, h3798, hlam]
                      · linarith only [h2860, h3798, hlam]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      rcases p3699_3 (m.d 0 2) (by simp) with h3801 | h3801
                      · linarith only [h0, h3801, hlam]
                      · linarith only [h2861, h3801, hlam]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h2859, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h3644, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h3649, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h3694, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h2860, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h3645, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h2858, h3646, h3696, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3699_1, u0elo0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h3696, hlam, p3699_1]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h2861, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h3646, hlam, p3699_0]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h0, h2858, h3646, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3699_1, u0elo1]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [h0, h2858, h3646, hc24, hlam, hphi, ht0b, ht45, ht5b, p3699_1, u0elo1]
                    · have p3699_0 := h3699c.1
                      have p3699_1 := h3699c.2.1
                      have p3699_2 := h3699c.2.2.1
                      have p3699_3 := h3699c.2.2.2
                      linarith only [hlam, p3699_0]
                  · rcases h2bigk with h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h0, hlam, p3819_1]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3822 | h3822
                      · rcases p3819_3 (m.d 1 2) (by simp) with h3823 | h3823
                        · rcases p3819_3 (m.d 2 3) (by simp) with h3824 | h3824
                          · linarith only [h3824, hlam, p3819_0]
                          · rcases p3819_3 (m.d 2 4) (by simp) with h3826 | h3826
                            · linarith only [h2860, h3826, hlam]
                            · linarith only [h3649, h3826, hlam]
                        · linarith only [h3644, h3823, hlam]
                      · linarith only [h3822, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3831 | h3831
                      · rcases p3819_3 (m.d 1 2) (by simp) with h3832 | h3832
                        · rcases p3819_3 (m.d 2 3) (by simp) with h3833 | h3833
                          · linarith only [h2859, h3833, hlam]
                          · rcases p3819_3 (m.d 2 4) (by simp) with h3835 | h3835
                            · linarith only [h3835, hlam, p3819_0]
                            · rcases p3819_3 (m.d 2 5) (by simp) with h3837 | h3837
                              · linarith only [h2861, h3837, hlam]
                              · linarith only [h3696, h3837, hlam]
                        · linarith only [h3645, h3832, hlam]
                      · linarith only [h3831, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3842 | h3842
                      · rcases p3819_3 (m.d 1 2) (by simp) with h3843 | h3843
                        · rcases p3819_3 (m.d 2 3) (by simp) with h3844 | h3844
                          · linarith only [h2859, h3844, hlam]
                          · rcases p3819_3 (m.d 2 4) (by simp) with h3846 | h3846
                            · linarith only [h2860, h3846, hlam]
                            · rcases p3819_3 (m.d 2 5) (by simp) with h3848 | h3848
                              · linarith only [h3848, hlam, p3819_0]
                              · rcases h5bigk with h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [hlam, p3850_0]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p3850_1, u0elo4]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h0, h2858, hc25, hlam, hphi, ht0b, ht5b, p3850_1, u0elo1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h2862, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3393, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h2858, hlam, p3850_0]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [hlam, p3850_0]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h0, h2858, hc25, hlam, hphi, ht0b, ht5b, p3850_1, u0elo1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h0, h2858, h2862, hc05, hlam, hphi, ht0b, ht5b, p3850_1, u0elo1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3647, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h2861, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3646, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [hlam, p3850_0]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3694, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3696, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h2861, h3649, h3696, hc23, hc35, hlam, hphi, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hc35, hlam, hphi, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3649, h3696, hc23, hc35, hlam, hphi, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [hlam, p3850_0]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3698, hlam, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h2858, h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [h2859, h2862, hc23, hc45, hlam, hphi, ht34, p3850_1]
                                · have p3850_0 := h3850c.1
                                  have p3850_1 := h3850c.2.1
                                  have p3850_2 := h3850c.2.2.1
                                  have p3850_3 := h3850c.2.2.2
                                  linarith only [hlam, p3850_0]
                        · linarith only [h3646, h3843, hlam]
                      · linarith only [h3842, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3878 | h3878
                      · linarith only [h0, h3878, hlam]
                      · rcases p3819_3 (m.d 1 2) (by simp) with h3880 | h3880
                        · rcases p3819_3 (m.d 2 3) (by simp) with h3881 | h3881
                          · linarith only [h3644, h3881, hlam]
                          · rcases p3819_3 (m.d 2 4) (by simp) with h3883 | h3883
                            · linarith only [h3645, h3883, hlam]
                            · rcases p3819_3 (m.d 2 5) (by simp) with h3885 | h3885
                              · linarith only [h3646, h3885, hlam]
                              · rcases h5bigk with h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [hlam, p3887_0]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3887_1, u0elo4]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h0, h2858, h3649, h3696, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3819_1, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h2862, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3393, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h2858, hlam, p3887_0]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [hlam, p3887_0]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h0, h2858, h3649, h3696, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3819_1, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h0, h2858, h2862, h3393, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3819_1, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3647, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h2861, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3646, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [hlam, p3887_0]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3694, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3696, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h2860, h3393, h3649, hc23, hc35, hlam, hphi, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3646, h3649, h3696, h3698, hc23, hc45, hlam, hphi, ht34, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3649, h3696, h3698, hc23, hc45, hlam, hphi, ht34, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [hlam, p3887_0]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3698, hlam, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h2858, h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3646, h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h3649, h3696, hc23, hc45, hlam, hphi, ht34, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [h2859, h2862, hc23, hc45, hlam, hphi, ht34, p3887_1]
                                · have p3887_0 := h3887c.1
                                  have p3887_1 := h3887c.2.1
                                  have p3887_2 := h3887c.2.2.1
                                  have p3887_3 := h3887c.2.2.2
                                  linarith only [hlam, p3887_0]
                        · linarith only [h0, h3880, hlam]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3915 | h3915
                      · linarith only [h0, h3915, hlam]
                      · linarith only [h2859, h3915, hlam]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3918 | h3918
                      · linarith only [h0, h3918, hlam]
                      · linarith only [h2860, h3918, hlam]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      rcases p3819_3 (m.d 0 2) (by simp) with h3921 | h3921
                      · linarith only [h0, h3921, hlam]
                      · linarith only [h2861, h3921, hlam]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h2859, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h3644, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h3649, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h3694, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h2860, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h3645, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h2858, h3646, h3696, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3819_1, u0elo0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h3696, hlam, p3819_1]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h2861, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h3646, hlam, p3819_0]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h0, h2858, h3646, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3819_1, u0elo1]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [h0, h2858, h3646, hc24, hlam, hphi, ht0b, ht45, ht5b, p3819_1, u0elo1]
                    · have p3819_0 := h3819c.1
                      have p3819_1 := h3819c.2.1
                      have p3819_2 := h3819c.2.2.1
                      have p3819_3 := h3819c.2.2.2
                      linarith only [hlam, p3819_0]
        · linarith only [h0, h2861, h3646, hlam]
      · linarith only [h0, h2858, h2860, h3645, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
    · linarith only [h0, h2859, h2862, h3644, hc01, hc35, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2860 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2861 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h2862 | h2862
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 h2858 h2859 h2860 h2861 h2862
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 h2858 h2859 h2860 h2861 h2862

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2860 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2861 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h2858, h2861, hlam]

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2860 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h2861 | h2861
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 h2858 h2859 h2860 h2861
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 h2858 h2859 h2860 h2861

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2860 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h3943 | h3943
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3944 | h3944
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3945 | h3945
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3946 | h3946
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3947 | h3947
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3948 | h3948
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3949 | h3949
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3950 | h3950
                · linarith only [h2859, h2860, h3947, h3950, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3952 | h3952
                  · linarith only [h2859, h2860, h3947, h3952, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h2859, h2860, h3944, h3947, h3952, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h2859, h2860, h3947, h3949, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h2860, h3947, h3948, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3957 | h3957
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3958 | h3958
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3959 | h3959
                · linarith only [h0, h2859, h3947, h3959, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3961 | h3961
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3962 | h3962
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3963 | h3963
                      · rcases h2bigk with h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c | h3964c
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h0, hlam, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h0, h3947, h3959, hc23, hc34, hlam, hphi, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h2860, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          rcases p3964_3 (m.d 0 2) (by simp) with h3969 | h3969
                          · rcases p3964_3 (m.d 1 2) (by simp) with h3970 | h3970
                            · rcases p3964_3 (m.d 2 3) (by simp) with h3971 | h3971
                              · linarith only [h2859, h3971, hlam]
                              · linarith only [h3961, h3971, hlam]
                            · linarith only [h3957, h3970, hlam]
                          · linarith only [h3969, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3947, h3959, hc02, hc34, hlam, hphi, ht23, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3947, h3959, h3961, h3963, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3947, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          rcases p3964_3 (m.d 0 2) (by simp) with h3980 | h3980
                          · linarith only [h0, h3980, hlam]
                          · linarith only [h3943, h3980, hlam]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h2859, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3946, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3959, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h2859, h3961, h3963, hc45, hlam, hphi, ht0b, ht5b, p3964_1, u0elo1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h2859, h3959, hc23, hc34, hlam, hphi, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h0, h2858, h3957, h3959, h3961, h3963, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          rcases p3964_3 (m.d 0 2) (by simp) with h3990 | h3990
                          · linarith only [h2860, h3990, hlam]
                          · linarith only [h2859, h3990, hlam]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h0, h2858, h3947, h3957, hlam, p3964_2]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3943, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3957, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3961, hlam, p3964_1]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [h3962, hlam, p3964_0]
                        · have p3964_0 := h3964c.1
                          have p3964_1 := h3964c.2.1
                          have p3964_2 := h3964c.2.2.1
                          have p3964_3 := h3964c.2.2.2
                          linarith only [hlam, p3964_0]
                      · linarith only [h0, h2858, h3947, h3958, h3963, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h2858, h3947, h3958, h3962, hlam]
                  · linarith only [h0, h2859, h3944, h3947, h3959, h3961, hc23, hc34, hlam, hphi]
              · linarith only [h0, h2858, h3945, h3947, h3957, h3958, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h0, h3943, h3957, hlam]
        · linarith only [h0, h2859, h3946, hlam]
      · linarith only [h0, h2858, h2860, h3945, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4007 | h4007
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4008 | h4008
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4009 | h4009
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4010 | h4010
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4011 | h4011
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4012 | h4012
                · linarith only [h2859, h2860, h4009, h4012, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4014 | h4014
                  · linarith only [h2859, h2860, h3944, h4009, h4014, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4016 | h4016
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4017 | h4017
                      · rcases h2bigk with h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c | h4018c
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h0, hlam, p4018_1]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2860, h4009, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4018_1]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2860, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2860, h4009, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4018_1]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          rcases p4018_3 (m.d 0 2) (by simp) with h4024 | h4024
                          · linarith only [h0, h4024, hlam]
                          · rcases p4018_3 (m.d 1 2) (by simp) with h4026 | h4026
                            · rcases p4018_3 (m.d 2 3) (by simp) with h4027 | h4027
                              · linarith only [h4008, h4027, hlam]
                              · rcases p4018_3 (m.d 2 4) (by simp) with h4029 | h4029
                                · linarith only [h4009, h4029, hlam]
                                · linarith only [h2860, h4029, hlam]
                            · linarith only [h0, h4026, hlam]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2859, h2860, h4009, hlam, p4018_2]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h0, h2860, hc01, hc12, hlam, hphi, p4018_1]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2860, h3943, h4009, hlam, p4018_2]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2859, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h4008, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h4012, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h4014, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h3943, h4012, h4014, hc23, hc34, hlam, hphi, p4018_1]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h4009, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          rcases p4018_3 (m.d 0 2) (by simp) with h4044 | h4044
                          · linarith only [h2860, h4044, hlam]
                          · linarith only [h2859, h4044, hlam]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          rcases p4018_3 (m.d 0 2) (by simp) with h4048 | h4048
                          · linarith only [h2860, h4048, hlam]
                          · linarith only [h3943, h4048, hlam]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h3943, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h4010, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h2858, h4010, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4018_1, u0elo0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [h4016, hlam, p4018_0]
                        · have p4018_0 := h4018c.1
                          have p4018_1 := h4018c.2.1
                          have p4018_2 := h4018c.2.2.1
                          have p4018_3 := h4018c.2.2.2
                          linarith only [hlam, p4018_0]
                      · linarith only [h0, h2858, h2860, h4009, h4011, h4017, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h2858, h2860, h4011, h4016, hlam]
              · linarith only [h2859, h2860, h4009, h4011, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h2860, h4009, h4010, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4060 | h4060
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4061 | h4061
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4062 | h4062
                · linarith only [h0, h2858, h2859, h3944, h4009, h4062, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4064 | h4064
                  · linarith only [h2859, h3944, h4064, hlam]
                  · linarith only [h0, h2858, h4009, h4060, h4062, h4064, hc23, hc34, hlam, hphi]
              · linarith only [h0, h4007, h4009, h4061, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h0, h2858, h3943, h4060, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
        · linarith only [h0, h2859, h4008, hlam]
      · linarith only [h0, h2858, h2860, h4007, hlam]
  · linarith only [h0, h2858, h3943, hlam]

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h2860 | h2860
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0 m hb0 hb2 hb5 hg0 h2858 h2859 h2860
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x1 m hb0 hb2 hb5 hg0 h2858 h2859 h2860

end R2N4
