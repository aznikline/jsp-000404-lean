import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3367 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3368 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3369 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h3370 | h3370
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3371 | h3371
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3372 | h3372
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3373 | h3373
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3374 | h3374
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3375 | h3375
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3376 | h3376
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3377 | h3377
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3378 | h3378
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3379 | h3379
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3380 | h3380
                      · linarith only [h0, h3363, h3372, h3377, h3380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h3363, h3373, h3375, h3379, h3380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3383 | h3383
                      · linarith only [h3377, h3379, h3383, hlam]
                      · rcases h0bigk with h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h0, hlam, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h0, h3369, h3371, h3377, h3379, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h0, h3371, h3377, h3379, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h0, h3371, h3377, h3379, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3363, h3372, h3378, hc02, hc35, hlam, hphi, ht0b, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3369, h3371, h3377, h3379, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h0, h3371, h3377, h3379, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          rcases p3385_3 (m.d 0 1) (by simp) with h3395 | h3395
                          · linarith only [h0, h3395, hlam]
                          · linarith only [h3365, h3395, hlam]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3363, hlam, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3366, hlam, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3371, h3377, h3379, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3385_1, u3elo0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3371, h3377, h3379, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3385_1, u3elo0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3364, hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3367, hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3369, hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h0, h3364, h3371, h3377, h3379, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3365, hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3368, hlam, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3370, hlam, p3385_0]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [h3371, hlam, p3385_1]
                        · have p3385_0 := h3385c.1
                          have p3385_1 := h3385c.2.1
                          have p3385_2 := h3385c.2.2.1
                          have p3385_3 := h3385c.2.2.2
                          linarith only [hlam, p3385_0]
                  · linarith only [h3370, h3378, hc23, hlam, hphi, u3elo0]
                · linarith only [h3369, h3377, hc23, hlam, hphi, u3elo0]
              · linarith only [h3370, h3376, hc13, hlam, hphi, u3elo0]
            · linarith only [h3369, h3372, h3375, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h3368, h3374, hlam]
        · linarith only [h0, h3367, h3373, hlam]
      · linarith only [h0, h3372, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3420 | h3420
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3421 | h3421
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3422 | h3422
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3423 | h3423
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3424 | h3424
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3425 | h3425
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3426 | h3426
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3427 | h3427
                    · linarith only [h0, h3363, h3371, h3421, h3423, h3427, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3429 | h3429
                      · linarith only [h0, h3363, h3371, h3420, h3425, h3429, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h0, hlam, p3431_1]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h0, h3363, h3420, h3426, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3431_1]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3435 | h3435
                          · rcases p3431_3 (m.d 0 2) (by simp) with h3436 | h3436
                            · rcases p3431_3 (m.d 0 3) (by simp) with h3437 | h3437
                              · linarith only [h3363, h3437, hlam]
                              · linarith only [h3369, h3437, hlam]
                            · linarith only [h3367, h3436, hlam]
                          · linarith only [h3364, h3435, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3442 | h3442
                          · rcases p3431_3 (m.d 0 2) (by simp) with h3443 | h3443
                            · rcases p3431_3 (m.d 0 3) (by simp) with h3444 | h3444
                              · linarith only [h3363, h3444, hlam]
                              · linarith only [h3370, h3444, hlam]
                            · linarith only [h3368, h3443, hlam]
                          · linarith only [h3365, h3442, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h0, h3363, h3420, h3426, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3431_1]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3451 | h3451
                          · linarith only [h0, h3451, hlam]
                          · linarith only [h3363, h3451, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3454 | h3454
                          · linarith only [h0, h3454, hlam]
                          · linarith only [h3364, h3454, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3457 | h3457
                          · linarith only [h0, h3457, hlam]
                          · linarith only [h3365, h3457, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3363, hlam, p3431_1]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3366, hlam, p3431_1]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3463 | h3463
                          · rcases p3431_3 (m.d 0 2) (by simp) with h3464 | h3464
                            · rcases p3431_3 (m.d 0 3) (by simp) with h3465 | h3465
                              · rcases p3431_3 (m.d 0 4) (by simp) with h3466 | h3466
                                · linarith only [h3369, h3466, hlam]
                                · rcases p3431_3 (m.d 0 5) (by simp) with h3468 | h3468
                                  · linarith only [h3370, h3468, hlam]
                                  · linarith only [h3371, h3468, hlam]
                              · linarith only [h3369, h3465, hlam]
                            · linarith only [h3367, h3464, hlam]
                          · linarith only [h3364, h3463, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3474 | h3474
                          · rcases p3431_3 (m.d 0 2) (by simp) with h3475 | h3475
                            · rcases p3431_3 (m.d 0 3) (by simp) with h3476 | h3476
                              · rcases p3431_3 (m.d 0 4) (by simp) with h3477 | h3477
                                · linarith only [h3369, h3477, hlam]
                                · rcases p3431_3 (m.d 0 5) (by simp) with h3479 | h3479
                                  · linarith only [h3370, h3479, hlam]
                                  · rcases h0emin with h3481 | h3481 | h3481 | h3481 | h3481
                                    · linarith only [h0, h3481, hc12, hlam, ht01]
                                    · rcases h2bigk with h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, hlam, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 2) (by simp) with h3486 | h3486
                                        · rcases p3483_3 (m.d 1 2) (by simp) with h3487 | h3487
                                          · rcases p3483_3 (m.d 2 3) (by simp) with h3488 | h3488
                                            · linarith only [h3488, hlam, p3483_0]
                                            · rcases p3483_3 (m.d 2 4) (by simp) with h3490 | h3490
                                              · linarith only [h3367, h3490, hlam]
                                              · rcases p3483_3 (m.d 2 5) (by simp) with h3492 | h3492
                                                · linarith only [h3368, h3492, hlam]
                                                · rcases h2emin with h3494 | h3494 | h3494 | h3494 | h3494
                                                  · rcases h3bigk with h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3420, h3426, h3429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3495_1, u3elo0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3426, h3429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3495_1, u3elo0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      rcases p3495_3 (m.d 0 3) (by simp) with h3499 | h3499
                                                      · rcases p3495_3 (m.d 1 3) (by simp) with h3500 | h3500
                                                        · linarith only [h3363, h3500, hlam]
                                                        · linarith only [h3423, h3500, hlam]
                                                      · linarith only [h3499, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      rcases p3495_3 (m.d 0 3) (by simp) with h3504 | h3504
                                                      · rcases p3495_3 (m.d 1 3) (by simp) with h3505 | h3505
                                                        · linarith only [h3363, h3505, hlam]
                                                        · linarith only [h3424, h3505, hlam]
                                                      · linarith only [h3504, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3363, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3426, h3429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3495_1, u3elo1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h0, h3363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3495_1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h0, h3363, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3495_1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3366, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3420, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3483_1, p3495_1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h0, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3483_1, p3495_1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3369, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3423, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3425, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3429, hlam, p3495_1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3370, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3424, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h3426, hlam, p3495_0]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [h0, h3365, h3422, h3426, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3495_1]
                                                    · have p3495_0 := h3495c.1
                                                      have p3495_1 := h3495c.2.1
                                                      have p3495_2 := h3495c.2.2.1
                                                      have p3495_3 := h3495c.2.2.2
                                                      linarith only [hlam, p3495_0]
                                                  · rcases h3bigk with h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c | h3529c
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hc13, hlam, hphi, p3529_1, u3elo0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p3529_1, u3elo0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      rcases p3529_3 (m.d 0 3) (by simp) with h3533 | h3533
                                                      · rcases p3529_3 (m.d 1 3) (by simp) with h3534 | h3534
                                                        · linarith only [h3363, h3534, hlam]
                                                        · linarith only [h3423, h3534, hlam]
                                                      · linarith only [h3533, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      rcases p3529_3 (m.d 0 3) (by simp) with h3538 | h3538
                                                      · rcases p3529_3 (m.d 1 3) (by simp) with h3539 | h3539
                                                        · linarith only [h3363, h3539, hlam]
                                                        · linarith only [h3424, h3539, hlam]
                                                      · linarith only [h3538, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3363, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3426, h3429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3529_1, u3elo1]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h0, h3363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3529_1]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h0, h3363, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3529_1]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3366, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3420, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3483_1, p3529_1]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h0, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3483_1, p3529_1]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3369, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3423, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3425, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3429, hlam, p3529_1]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3370, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3424, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3426, hlam, p3529_0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [h3370, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3529_1, u3elo0]
                                                    · have p3529_0 := h3529c.1
                                                      have p3529_1 := h3529c.2.1
                                                      have p3529_2 := h3529c.2.2.1
                                                      have p3529_3 := h3529c.2.2.2
                                                      linarith only [hlam, p3529_0]
                                                  · linarith only [h0, h3494, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3483_1]
                                                  · linarith only [h3364, h3371, h3421, h3494, hc45, hlam, ht23, ht34]
                                                  · linarith only [h3365, h3422, h3494, hlam, ht23, p3431_1, u3elo0]
                                          · linarith only [h3420, h3487, hlam]
                                        · linarith only [h3486, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 2) (by simp) with h3568 | h3568
                                        · rcases p3483_3 (m.d 1 2) (by simp) with h3569 | h3569
                                          · rcases p3483_3 (m.d 2 3) (by simp) with h3570 | h3570
                                            · linarith only [h3366, h3570, hlam]
                                            · linarith only [h3425, h3570, hlam]
                                          · linarith only [h3421, h3569, hlam]
                                        · linarith only [h3568, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 2) (by simp) with h3575 | h3575
                                        · rcases p3483_3 (m.d 1 2) (by simp) with h3576 | h3576
                                          · rcases p3483_3 (m.d 2 3) (by simp) with h3577 | h3577
                                            · linarith only [h3366, h3577, hlam]
                                            · linarith only [h3426, h3577, hlam]
                                          · linarith only [h3422, h3576, hlam]
                                        · linarith only [h3575, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3481, hc12, hlam, ht01, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 2) (by simp) with h3584 | h3584
                                        · linarith only [h0, h3584, hlam]
                                        · linarith only [h3366, h3584, hlam]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h3363, h3364, h3371, h3421, hlam, p3431_1, p3483_2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h3363, h3368, hlam, p3431_1, p3483_2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3366, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3420, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h3363, h3420, h3425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h3363, h3420, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3367, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3421, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3425, hlam, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3427, hlam, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3368, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3422, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3426, hlam, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3368, h3425, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3431_1, p3483_1, u3elo0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                    · linarith only [h3481, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h0, h3364, h3481, hc12, hlam, ht01]
                                    · linarith only [h3481, hlam, ht01, ht12, ht23, p3431_1, u3elo0]
                              · linarith only [h3370, h3476, hlam]
                            · linarith only [h3368, h3475, hlam]
                          · linarith only [h3365, h3474, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3364, hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3367, hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3369, hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3371, hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3365, hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3368, hlam, p3431_1]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [h3370, hlam, p3431_0]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          rcases p3431_3 (m.d 0 1) (by simp) with h3618 | h3618
                          · rcases p3431_3 (m.d 0 2) (by simp) with h3619 | h3619
                            · rcases p3431_3 (m.d 0 3) (by simp) with h3620 | h3620
                              · rcases p3431_3 (m.d 0 4) (by simp) with h3621 | h3621
                                · linarith only [h3371, h3621, hlam]
                                · rcases p3431_3 (m.d 0 5) (by simp) with h3623 | h3623
                                  · rcases h0emin with h3624 | h3624 | h3624 | h3624 | h3624
                                    · linarith only [h0, h3624, hc12, hlam, ht01]
                                    · rcases h2bigk with h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c | h3626c
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h0, hlam, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        rcases p3626_3 (m.d 0 2) (by simp) with h3629 | h3629
                                        · rcases p3626_3 (m.d 1 2) (by simp) with h3630 | h3630
                                          · rcases p3626_3 (m.d 2 3) (by simp) with h3631 | h3631
                                            · linarith only [h3631, hlam, p3626_0]
                                            · rcases p3626_3 (m.d 2 4) (by simp) with h3633 | h3633
                                              · linarith only [h3367, h3633, hlam]
                                              · rcases p3626_3 (m.d 2 5) (by simp) with h3635 | h3635
                                                · linarith only [h3368, h3635, hlam]
                                                · rcases h2emin with h3637 | h3637 | h3637 | h3637 | h3637
                                                  · rcases h3bigk with h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c | h3638c
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hc13, hlam, hphi, p3638_1, u3elo0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p3638_1, u3elo0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      rcases p3638_3 (m.d 0 3) (by simp) with h3642 | h3642
                                                      · rcases p3638_3 (m.d 1 3) (by simp) with h3643 | h3643
                                                        · linarith only [h3363, h3643, hlam]
                                                        · linarith only [h3423, h3643, hlam]
                                                      · linarith only [h3642, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      rcases p3638_3 (m.d 0 3) (by simp) with h3647 | h3647
                                                      · rcases p3638_3 (m.d 1 3) (by simp) with h3648 | h3648
                                                        · linarith only [h3363, h3648, hlam]
                                                        · linarith only [h3424, h3648, hlam]
                                                      · linarith only [h3647, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3363, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3426, h3429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3638_1, u3elo1]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h0, h3363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3638_1]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h0, h3363, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3638_1]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3366, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3420, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3626_1, p3638_1]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h0, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3626_1, p3638_1]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3369, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3423, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3425, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3429, hlam, p3638_1]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3370, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3424, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3426, hlam, p3638_0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [h3370, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3638_1, u3elo0]
                                                    · have p3638_0 := h3638c.1
                                                      have p3638_1 := h3638c.2.1
                                                      have p3638_2 := h3638c.2.2.1
                                                      have p3638_3 := h3638c.2.2.2
                                                      linarith only [hlam, p3638_0]
                                                  · rcases h3bigk with h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hc13, hlam, hphi, p3672_1, u3elo0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p3672_1, u3elo0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      rcases p3672_3 (m.d 0 3) (by simp) with h3676 | h3676
                                                      · rcases p3672_3 (m.d 1 3) (by simp) with h3677 | h3677
                                                        · linarith only [h3363, h3677, hlam]
                                                        · linarith only [h3423, h3677, hlam]
                                                      · linarith only [h3676, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      rcases p3672_3 (m.d 0 3) (by simp) with h3681 | h3681
                                                      · rcases p3672_3 (m.d 1 3) (by simp) with h3682 | h3682
                                                        · linarith only [h3363, h3682, hlam]
                                                        · linarith only [h3424, h3682, hlam]
                                                      · linarith only [h3681, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3363, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3426, h3429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3672_1, u3elo1]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h0, h3363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3672_1]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h0, h3363, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3672_1]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3366, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3420, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3626_1, p3672_1]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h0, h3429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3626_1, p3672_1]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3369, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3423, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3425, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3429, hlam, p3672_1]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3370, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3424, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3426, hlam, p3672_0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [h3370, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3672_1, u3elo0]
                                                    · have p3672_0 := h3672c.1
                                                      have p3672_1 := h3672c.2.1
                                                      have p3672_2 := h3672c.2.2.1
                                                      have p3672_3 := h3672c.2.2.2
                                                      linarith only [hlam, p3672_0]
                                                  · linarith only [h0, h3637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3626_1]
                                                  · linarith only [h3364, h3421, h3637, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3431_1]
                                                  · linarith only [h0, h3363, h3422, h3424, h3637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                          · linarith only [h3420, h3630, hlam]
                                        · linarith only [h3629, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        rcases p3626_3 (m.d 0 2) (by simp) with h3711 | h3711
                                        · rcases p3626_3 (m.d 1 2) (by simp) with h3712 | h3712
                                          · rcases p3626_3 (m.d 2 3) (by simp) with h3713 | h3713
                                            · linarith only [h3366, h3713, hlam]
                                            · linarith only [h3425, h3713, hlam]
                                          · linarith only [h3421, h3712, hlam]
                                        · linarith only [h3711, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        rcases p3626_3 (m.d 0 2) (by simp) with h3718 | h3718
                                        · rcases p3626_3 (m.d 1 2) (by simp) with h3719 | h3719
                                          · rcases p3626_3 (m.d 2 3) (by simp) with h3720 | h3720
                                            · linarith only [h3366, h3720, hlam]
                                            · linarith only [h3426, h3720, hlam]
                                          · linarith only [h3422, h3719, hlam]
                                        · linarith only [h3718, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3624, hc12, hlam, ht01, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        rcases p3626_3 (m.d 0 2) (by simp) with h3727 | h3727
                                        · linarith only [h0, h3727, hlam]
                                        · linarith only [h3366, h3727, hlam]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h0, h3363, h3364, h3370, h3421, hlam, p3431_1, p3626_2]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        rcases p3626_3 (m.d 0 2) (by simp) with h3731 | h3731
                                        · linarith only [h0, h3731, hlam]
                                        · linarith only [h3368, h3731, hlam]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3366, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3420, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h0, h3363, h3420, h3425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h0, h3363, h3420, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3367, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3421, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3425, hlam, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3427, hlam, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3368, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3422, hlam, p3626_0]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h3426, hlam, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [h0, h3363, h3422, h3424, h3425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3626_1]
                                      · have p3626_0 := h3626c.1
                                        have p3626_1 := h3626c.2.1
                                        have p3626_2 := h3626c.2.2.1
                                        have p3626_3 := h3626c.2.2.2
                                        linarith only [hlam, p3626_0]
                                    · linarith only [h3624, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h3624, hc05, hlam, p3431_1]
                                    · linarith only [h0, h3365, h3624, hc12, hlam, ht01]
                                  · linarith only [h3371, h3623, hlam]
                              · linarith only [h3369, h3620, hlam]
                            · linarith only [h3367, h3619, hlam]
                          · linarith only [h3364, h3618, hlam]
                        · have p3431_0 := h3431c.1
                          have p3431_1 := h3431c.2.1
                          have p3431_2 := h3431c.2.2.1
                          have p3431_3 := h3431c.2.2.2
                          linarith only [hlam, p3431_0]
                  · linarith only [h3370, h3426, hc23, hlam, hphi, u3elo0]
                · linarith only [h3369, h3425, hc23, hlam, hphi, u3elo0]
              · linarith only [h3370, h3424, hc13, hlam, hphi, u3elo0]
            · linarith only [h3369, h3420, h3423, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h3363, h3368, h3420, h3422, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h3367, h3421, hlam]
      · linarith only [h0, h3363, h3420, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3764 | h3764
    · linarith only [h3369, h3370, h3764, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3766 | h3766
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3767 | h3767
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3768 | h3768
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3769 | h3769
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3770 | h3770
              · linarith only [h3363, h3370, h3770, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3772 | h3772
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3773 | h3773
                  · linarith only [h3363, h3370, h3766, h3773, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3775 | h3775
                    · linarith only [h3364, h3764, h3767, h3775, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3777 | h3777
                      · linarith only [h3365, h3764, h3766, h3770, h3772, h3777, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h0, hlam, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h0, h3369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          rcases p3779_3 (m.d 0 1) (by simp) with h3783 | h3783
                          · rcases p3779_3 (m.d 0 2) (by simp) with h3784 | h3784
                            · rcases p3779_3 (m.d 0 3) (by simp) with h3785 | h3785
                              · linarith only [h3363, h3785, hlam]
                              · linarith only [h3369, h3785, hlam]
                            · linarith only [h3367, h3784, hlam]
                          · linarith only [h3364, h3783, hlam]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h0, h3363, h3370, h3766, h3772, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h0, h3363, h3766, h3772, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          rcases p3779_3 (m.d 0 1) (by simp) with h3793 | h3793
                          · linarith only [h0, h3793, hlam]
                          · linarith only [h3363, h3793, hlam]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          rcases p3779_3 (m.d 0 1) (by simp) with h3796 | h3796
                          · linarith only [h0, h3796, hlam]
                          · linarith only [h3364, h3796, hlam]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          rcases p3779_3 (m.d 0 1) (by simp) with h3799 | h3799
                          · linarith only [h0, h3799, hlam]
                          · linarith only [h3365, h3799, hlam]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3363, hlam, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3366, hlam, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3364, h3370, h3767, h3772, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3779_1, u3elo4]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3370, hlam, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3364, hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3367, hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3369, hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3764, hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3365, hlam, p3779_0]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h3368, hlam, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [h0, h3363, h3365, h3766, h3772, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          rcases p3779_3 (m.d 0 1) (by simp) with h3815 | h3815
                          · rcases p3779_3 (m.d 0 2) (by simp) with h3816 | h3816
                            · rcases p3779_3 (m.d 0 3) (by simp) with h3817 | h3817
                              · linarith only [h3370, h3817, hlam]
                              · linarith only [h3369, h3817, hlam]
                            · linarith only [h3367, h3816, hlam]
                          · linarith only [h3364, h3815, hlam]
                        · have p3779_0 := h3779c.1
                          have p3779_1 := h3779c.2.1
                          have p3779_2 := h3779c.2.2.1
                          have p3779_3 := h3779c.2.2.2
                          linarith only [hlam, p3779_0]
                · linarith only [h3369, h3772, hc23, hlam, hphi, u3elo0]
            · linarith only [h3369, h3370, h3766, h3769, hc23, hlam, hphi, u3elo4]
          · linarith only [h0, h3368, h3768, hlam]
        · linarith only [h0, h3367, h3767, hlam]
      · linarith only [h0, h3363, h3766, hc13, hlam, hphi, u3elo2]

end R2N4
