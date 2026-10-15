import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S4
import Jsp000404.R1LeavesN7_2S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8110000 in
set_option maxHeartbeats 8110000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s8_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2520 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h3334 | h3334
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3335 | h3335
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3336 | h3336
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3337 | h3337
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3338 | h3338
          · linarith only [h2, h3338, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3340 | h3340
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3341 | h3341
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3342 | h3342
                · linarith only [h2, h3334, h3342, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3344 | h3344
                  · linarith only [h2, h3334, h3340, h3344, h9, hlam]
                  · rcases h0bigk with h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h2520, h3335, h3340, h3342, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3346_1]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h2520, h3335, h3340, h3342, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3346_1]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3350 | h3350
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3351 | h3351
                        · linarith only [h0, h3351, hlam]
                        · linarith only [h3351, h5, hlam]
                      · linarith only [h2, h3350, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3355 | h3355
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3356 | h3356
                        · linarith only [h0, h3356, hlam]
                        · linarith only [h3356, h6, hlam]
                      · linarith only [h3, h3355, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h0, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h0, h2520, h3335, h3340, h3342, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3346_1]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3363 | h3363
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3364 | h3364
                        · rcases p3346_3 (m.d 0 3) (by simp) with h3365 | h3365
                          · linarith only [h3365, h4, hlam]
                          · linarith only [h3365, h7, hlam]
                        · linarith only [h3364, h5, hlam]
                      · linarith only [h2, h3363, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3370 | h3370
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3371 | h3371
                        · rcases p3346_3 (m.d 0 3) (by simp) with h3372 | h3372
                          · linarith only [h3372, h4, hlam]
                          · linarith only [h3372, h8, hlam]
                        · linarith only [h3371, h6, hlam]
                      · linarith only [h3, h3370, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h1, hlam, p3346_1]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h4, hlam, p3346_1]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3380 | h3380
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3381 | h3381
                        · rcases p3346_3 (m.d 0 3) (by simp) with h3382 | h3382
                          · rcases p3346_3 (m.d 0 4) (by simp) with h3383 | h3383
                            · linarith only [h3383, h7, hlam]
                            · rcases p3346_3 (m.d 0 5) (by simp) with h3385 | h3385
                              · linarith only [h3385, h8, hlam]
                              · linarith only [h3385, h9, hlam]
                          · linarith only [h3382, h7, hlam]
                        · linarith only [h3381, h5, hlam]
                      · linarith only [h2, h3380, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3391 | h3391
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3392 | h3392
                        · rcases p3346_3 (m.d 0 3) (by simp) with h3393 | h3393
                          · rcases p3346_3 (m.d 0 4) (by simp) with h3394 | h3394
                            · linarith only [h3394, h7, hlam]
                            · rcases p3346_3 (m.d 0 5) (by simp) with h3396 | h3396
                              · linarith only [h3396, h8, hlam]
                              · rcases h2bigk with h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c | h3398c
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  rcases p3398_3 (m.d 0 2) (by simp) with h3400 | h3400
                                  · rcases p3398_3 (m.d 1 2) (by simp) with h3401 | h3401
                                    · linarith only [h0, h3401, hlam]
                                    · rcases p3398_3 (m.d 2 3) (by simp) with h3403 | h3403
                                      · linarith only [h3403, h4, hlam]
                                      · linarith only [h2520, h3403, hlam]
                                  · linarith only [h0, h3400, hlam]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h0, h2520, h3335, h3340, h3342, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h2520, h3335, h3342, h4, hlam, p3398_2]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h2520, h3335, h4, hlam, p3398_2]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h0, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h2520, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h2520, h3340, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h0, h2520, h3340, h3342, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h4, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h0, h3334, h3340, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  rcases p3398_3 (m.d 0 2) (by simp) with h3418 | h3418
                                  · rcases p3398_3 (m.d 1 2) (by simp) with h3419 | h3419
                                    · linarith only [h2520, h3419, hlam]
                                    · linarith only [h3334, h3419, hlam]
                                  · linarith only [h3418, h5, hlam]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  rcases p3398_3 (m.d 0 2) (by simp) with h3423 | h3423
                                  · rcases p3398_3 (m.d 1 2) (by simp) with h3424 | h3424
                                    · linarith only [h2520, h3424, hlam]
                                    · linarith only [h3335, h3424, hlam]
                                  · linarith only [h3423, h6, hlam]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h5, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h3334, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h3340, hlam, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h3342, hlam, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h6, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h3335, hlam, p3398_0]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h3341, hlam, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [h0, h3335, h3340, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3398_1]
                                · have p3398_0 := h3398c.1
                                  have p3398_1 := h3398c.2.1
                                  have p3398_2 := h3398c.2.2.1
                                  have p3398_3 := h3398c.2.2.2
                                  linarith only [hlam, p3398_0]
                          · linarith only [h3393, h8, hlam]
                        · linarith only [h3392, h6, hlam]
                      · linarith only [h3, h3391, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h2, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h5, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h7, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h9, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h3, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h6, hlam, p3346_1]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [h8, hlam, p3346_0]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      rcases p3346_3 (m.d 0 1) (by simp) with h3449 | h3449
                      · rcases p3346_3 (m.d 0 2) (by simp) with h3450 | h3450
                        · rcases p3346_3 (m.d 0 3) (by simp) with h3451 | h3451
                          · rcases p3346_3 (m.d 0 4) (by simp) with h3452 | h3452
                            · linarith only [h3452, h9, hlam]
                            · rcases p3346_3 (m.d 0 5) (by simp) with h3454 | h3454
                              · rcases h2bigk with h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c | h3455c
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  rcases p3455_3 (m.d 0 2) (by simp) with h3457 | h3457
                                  · rcases p3455_3 (m.d 1 2) (by simp) with h3458 | h3458
                                    · linarith only [h0, h3458, hlam]
                                    · rcases p3455_3 (m.d 2 3) (by simp) with h3460 | h3460
                                      · linarith only [h3460, h4, hlam]
                                      · linarith only [h2520, h3460, hlam]
                                  · linarith only [h0, h3457, hlam]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h0, h2520, h3335, hc01, hc25, hlam, hphi, ht0b, ht5b, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h2520, h3334, h4, hlam, p3455_2]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h2520, h3335, h4, hlam, p3455_2]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h0, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h2520, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h0, h2520, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h0, h2520, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h4, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h0, h3334, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  rcases p3455_3 (m.d 0 2) (by simp) with h3475 | h3475
                                  · rcases p3455_3 (m.d 1 2) (by simp) with h3476 | h3476
                                    · linarith only [h2520, h3476, hlam]
                                    · linarith only [h3334, h3476, hlam]
                                  · linarith only [h3475, h5, hlam]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  rcases p3455_3 (m.d 0 2) (by simp) with h3480 | h3480
                                  · rcases p3455_3 (m.d 1 2) (by simp) with h3481 | h3481
                                    · linarith only [h2520, h3481, hlam]
                                    · linarith only [h3335, h3481, hlam]
                                  · linarith only [h3480, h6, hlam]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h5, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h3334, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h3340, hlam, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h3342, hlam, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h6, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h3335, hlam, p3455_0]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h3341, hlam, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [h0, h3335, h3340, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3455_1]
                                · have p3455_0 := h3455c.1
                                  have p3455_1 := h3455c.2.1
                                  have p3455_2 := h3455c.2.2.1
                                  have p3455_3 := h3455c.2.2.2
                                  linarith only [hlam, p3455_0]
                              · linarith only [h3454, h9, hlam]
                          · linarith only [h3451, h7, hlam]
                        · linarith only [h3450, h5, hlam]
                      · linarith only [h2, h3449, hlam]
                    · have p3346_0 := h3346c.1
                      have p3346_1 := h3346c.2.1
                      have p3346_2 := h3346c.2.2.1
                      have p3346_3 := h3346c.2.2.2
                      linarith only [hlam, p3346_0]
              · linarith only [h0, h2520, h3335, h3341, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h2520, h3334, h3340, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h2520, h3335, h3337, hlam]
      · linarith only [h2520, h3334, h3336, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3504 | h3504
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3505 | h3505
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3506 | h3506
          · linarith only [h2, h3506, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3508 | h3508
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3509 | h3509
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3510 | h3510
                · linarith only [h3334, h3335, h3510, h6, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3512 | h3512
                  · linarith only [h3334, h3335, h3508, h3512, h6, h9, hlam]
                  · rcases h0bigk with h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c | h3514c
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h3334, h3335, h3508, h3509, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h3334, h3335, h3508, h3509, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      rcases p3514_3 (m.d 0 1) (by simp) with h3518 | h3518
                      · rcases p3514_3 (m.d 0 2) (by simp) with h3519 | h3519
                        · linarith only [h0, h3519, hlam]
                        · linarith only [h3519, h5, hlam]
                      · linarith only [h2, h3518, hlam]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h3334, h3335, h3508, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h0, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h3334, h3335, h3508, h3509, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      rcases p3514_3 (m.d 0 1) (by simp) with h3527 | h3527
                      · rcases p3514_3 (m.d 0 2) (by simp) with h3528 | h3528
                        · rcases p3514_3 (m.d 0 3) (by simp) with h3529 | h3529
                          · linarith only [h3529, h4, hlam]
                          · linarith only [h3529, h7, hlam]
                        · linarith only [h3528, h5, hlam]
                      · linarith only [h2, h3527, hlam]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h0, h3334, h3335, h3508, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h1, hlam, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h4, hlam, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      rcases p3514_3 (m.d 0 1) (by simp) with h3538 | h3538
                      · rcases p3514_3 (m.d 0 2) (by simp) with h3539 | h3539
                        · rcases p3514_3 (m.d 0 3) (by simp) with h3540 | h3540
                          · rcases p3514_3 (m.d 0 4) (by simp) with h3541 | h3541
                            · linarith only [h3541, h7, hlam]
                            · rcases p3514_3 (m.d 0 5) (by simp) with h3543 | h3543
                              · linarith only [h3543, h8, hlam]
                              · linarith only [h3543, h9, hlam]
                          · linarith only [h3540, h7, hlam]
                        · linarith only [h3539, h5, hlam]
                      · linarith only [h2, h3538, hlam]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h3334, h3335, h3508, h6, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h2, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h5, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h7, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h9, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h3, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h6, hlam, p3514_1]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [h8, hlam, p3514_0]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      rcases p3514_3 (m.d 0 1) (by simp) with h3558 | h3558
                      · rcases p3514_3 (m.d 0 2) (by simp) with h3559 | h3559
                        · rcases p3514_3 (m.d 0 3) (by simp) with h3560 | h3560
                          · rcases p3514_3 (m.d 0 4) (by simp) with h3561 | h3561
                            · linarith only [h3561, h9, hlam]
                            · rcases p3514_3 (m.d 0 5) (by simp) with h3563 | h3563
                              · rcases h2bigk with h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c | h3564c
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  rcases p3564_3 (m.d 0 2) (by simp) with h3566 | h3566
                                  · rcases p3564_3 (m.d 1 2) (by simp) with h3567 | h3567
                                    · linarith only [h0, h3567, hlam]
                                    · rcases p3564_3 (m.d 2 3) (by simp) with h3569 | h3569
                                      · linarith only [h3569, h4, hlam]
                                      · linarith only [h2520, h3569, hlam]
                                  · linarith only [h0, h3566, hlam]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h0, h3334, h3335, h3508, h3509, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3334, h3335, h3509, h4, hlam, p3564_2]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3334, h3335, h3508, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h0, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h2520, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h0, h3335, h3508, h3509, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3335, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h4, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h0, h3334, h3508, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  rcases p3564_3 (m.d 0 2) (by simp) with h3584 | h3584
                                  · rcases p3564_3 (m.d 1 2) (by simp) with h3585 | h3585
                                    · linarith only [h2520, h3585, hlam]
                                    · linarith only [h3334, h3585, hlam]
                                  · linarith only [h3584, h5, hlam]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h0, h3334, h3335, h3508, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h5, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3334, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3508, hlam, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3510, hlam, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h6, hlam, p3564_0]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h0, h3334, h3508, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [h3509, hlam, p3564_1]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  rcases p3564_3 (m.d 0 2) (by simp) with h3598 | h3598
                                  · rcases p3564_3 (m.d 1 2) (by simp) with h3599 | h3599
                                    · linarith only [h3335, h3599, hlam]
                                    · linarith only [h3334, h3599, hlam]
                                  · linarith only [h3598, h5, hlam]
                                · have p3564_0 := h3564c.1
                                  have p3564_1 := h3564c.2.1
                                  have p3564_2 := h3564c.2.2.1
                                  have p3564_3 := h3564c.2.2.2
                                  linarith only [hlam, p3564_0]
                              · linarith only [h3563, h9, hlam]
                          · linarith only [h3560, h7, hlam]
                        · linarith only [h3559, h5, hlam]
                      · linarith only [h2, h3558, hlam]
                    · have p3514_0 := h3514c.1
                      have p3514_1 := h3514c.2.1
                      have p3514_2 := h3514c.2.2.1
                      have p3514_3 := h3514c.2.2.2
                      linarith only [hlam, p3514_0]
              · linarith only [h2520, h3334, h3508, h3509, h8, h9, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2520, h3334, h3508, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3611 | h3611
          · linarith only [h2, h3611, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3613 | h3613
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3614 | h3614
              · linarith only [h0, h2520, h3334, h3505, h3613, h3614, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h2520, h3334, h3613, h3614, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2520, h3334, h3613, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h2520, h3334, h3504, h7, h9, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3619 | h3619
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3620 | h3620
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3621 | h3621
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3622 | h3622
          · linarith only [h3334, h3619, h3622, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3334, h3619, h3622, hlam]
        · linarith only [h2520, h3619, h3621, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3626 | h3626
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3627 | h3627
          · linarith only [h2520, h3619, h3620, h3627, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3334, h3619, h3627, hlam]
        · linarith only [h2520, h3619, h3626, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3631 | h3631
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3632 | h3632
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3633 | h3633
          · linarith only [h2, h3633, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3635 | h3635
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3636 | h3636
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3637 | h3637
                · linarith only [h3637, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3639 | h3639
                  · linarith only [h1, h3631, h3639, h5, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c | h3641c
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h3334, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3644 | h3644
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3645 | h3645
                        · linarith only [h0, h3645, hlam]
                        · linarith only [h3645, h4, hlam]
                      · linarith only [h1, h3644, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3649 | h3649
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3650 | h3650
                        · linarith only [h0, h3650, hlam]
                        · linarith only [h3650, h5, hlam]
                      · linarith only [h2, h3649, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3654 | h3654
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3655 | h3655
                        · linarith only [h0, h3655, hlam]
                        · linarith only [h3655, h6, hlam]
                      · linarith only [h3, h3654, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h0, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3661 | h3661
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3662 | h3662
                        · rcases p3641_3 (m.d 0 3) (by simp) with h3663 | h3663
                          · linarith only [h3663, h4, hlam]
                          · rcases p3641_3 (m.d 0 4) (by simp) with h3665 | h3665
                            · linarith only [h3665, h5, hlam]
                            · rcases p3641_3 (m.d 0 5) (by simp) with h3667 | h3667
                              · linarith only [h3667, h6, hlam]
                              · rcases h2bigk with h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c | h3669c
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h3334, h3636, h3637, h4, hlam, p3641_1, p3669_2]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  rcases p3669_3 (m.d 0 2) (by simp) with h3672 | h3672
                                  · rcases p3669_3 (m.d 1 2) (by simp) with h3673 | h3673
                                    · linarith only [h0, h3673, hlam]
                                    · rcases p3669_3 (m.d 2 3) (by simp) with h3675 | h3675
                                      · linarith only [h3675, hlam, p3669_0]
                                      · rcases p3669_3 (m.d 2 4) (by simp) with h3677 | h3677
                                        · linarith only [h3677, h5, hlam]
                                        · rcases p3669_3 (m.d 2 5) (by simp) with h3679 | h3679
                                          · linarith only [h3679, h6, hlam]
                                          · rcases h3bigk with h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c | h3681c
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, h3334, h3636, h3637, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, h3639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h1, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h2520, hlam, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, h2520, h3639, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h4, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h0, h3639, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h7, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h3631, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h3635, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h3639, hlam, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h8, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h3632, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h3636, hlam, p3681_0]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [h3632, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3681_1]
                                            · have p3681_0 := h3681c.1
                                              have p3681_1 := h3681c.2.1
                                              have p3681_2 := h3681c.2.2.1
                                              have p3681_3 := h3681c.2.2.2
                                              linarith only [hlam, p3681_0]
                                  · linarith only [h3672, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  rcases p3669_3 (m.d 0 2) (by simp) with h3708 | h3708
                                  · rcases p3669_3 (m.d 1 2) (by simp) with h3709 | h3709
                                    · linarith only [h0, h3709, hlam]
                                    · rcases p3669_3 (m.d 2 3) (by simp) with h3711 | h3711
                                      · linarith only [h3711, h4, hlam]
                                      · linarith only [h3635, h3711, hlam]
                                  · linarith only [h3708, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  rcases p3669_3 (m.d 0 2) (by simp) with h3715 | h3715
                                  · rcases p3669_3 (m.d 1 2) (by simp) with h3716 | h3716
                                    · linarith only [h0, h3716, hlam]
                                    · rcases p3669_3 (m.d 2 3) (by simp) with h3718 | h3718
                                      · linarith only [h3718, h4, hlam]
                                      · linarith only [h3636, h3718, hlam]
                                  · linarith only [h3715, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h0, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h2520, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h3334, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h3619, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h4, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h0, h3334, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h0, h3334, h3637, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h5, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h3635, hlam, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h3637, hlam, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h6, hlam, p3669_0]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h3636, hlam, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3669_1]
                                · have p3669_0 := h3669c.1
                                  have p3669_1 := h3669c.2.1
                                  have p3669_2 := h3669c.2.2.1
                                  have p3669_3 := h3669c.2.2.2
                                  linarith only [hlam, p3669_0]
                        · linarith only [h3662, h4, hlam]
                      · linarith only [h1, h3661, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3744 | h3744
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3745 | h3745
                        · rcases p3641_3 (m.d 0 3) (by simp) with h3746 | h3746
                          · linarith only [h3746, h4, hlam]
                          · linarith only [h3746, h7, hlam]
                        · linarith only [h3745, h5, hlam]
                      · linarith only [h2, h3744, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3751 | h3751
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3752 | h3752
                        · rcases p3641_3 (m.d 0 3) (by simp) with h3753 | h3753
                          · linarith only [h3753, h4, hlam]
                          · linarith only [h3753, h8, hlam]
                        · linarith only [h3752, h6, hlam]
                      · linarith only [h3, h3751, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h1, hlam, p3641_1]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h4, hlam, p3641_1]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3761 | h3761
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3762 | h3762
                        · rcases p3641_3 (m.d 0 3) (by simp) with h3763 | h3763
                          · rcases p3641_3 (m.d 0 4) (by simp) with h3764 | h3764
                            · linarith only [h3764, h7, hlam]
                            · rcases p3641_3 (m.d 0 5) (by simp) with h3766 | h3766
                              · linarith only [h3766, h8, hlam]
                              · linarith only [h3766, h9, hlam]
                          · linarith only [h3763, h7, hlam]
                        · linarith only [h3762, h5, hlam]
                      · linarith only [h2, h3761, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      rcases p3641_3 (m.d 0 1) (by simp) with h3772 | h3772
                      · rcases p3641_3 (m.d 0 2) (by simp) with h3773 | h3773
                        · rcases p3641_3 (m.d 0 3) (by simp) with h3774 | h3774
                          · rcases p3641_3 (m.d 0 4) (by simp) with h3775 | h3775
                            · linarith only [h3775, h7, hlam]
                            · rcases p3641_3 (m.d 0 5) (by simp) with h3777 | h3777
                              · linarith only [h3777, h8, hlam]
                              · rcases h2bigk with h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h3334, h4, h5, h9, hlam, p3641_1, p3779_2]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  rcases p3779_3 (m.d 0 2) (by simp) with h3782 | h3782
                                  · rcases p3779_3 (m.d 1 2) (by simp) with h3783 | h3783
                                    · linarith only [h0, h3783, hlam]
                                    · rcases p3779_3 (m.d 2 3) (by simp) with h3785 | h3785
                                      · linarith only [h3785, hlam, p3779_0]
                                      · rcases p3779_3 (m.d 2 4) (by simp) with h3787 | h3787
                                        · linarith only [h3787, h5, hlam]
                                        · rcases p3779_3 (m.d 2 5) (by simp) with h3789 | h3789
                                          · linarith only [h3789, h6, hlam]
                                          · rcases h3bigk with h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3631, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h4, hlam, p3779_2, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              rcases p3791_3 (m.d 0 3) (by simp) with h3795 | h3795
                                              · rcases p3791_3 (m.d 1 3) (by simp) with h3796 | h3796
                                                · linarith only [h1, h3796, hlam]
                                                · linarith only [h3631, h3796, hlam]
                                              · linarith only [h3795, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              rcases p3791_3 (m.d 0 3) (by simp) with h3800 | h3800
                                              · rcases p3791_3 (m.d 1 3) (by simp) with h3801 | h3801
                                                · linarith only [h1, h3801, hlam]
                                                · linarith only [h3632, h3801, hlam]
                                              · linarith only [h3800, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h1, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h2520, hlam, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h1, h3639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h4, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3779_1, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3779_1, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h0, h3639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3779_1, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h7, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3631, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3635, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3639, hlam, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h8, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3632, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3636, hlam, p3791_0]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [h3632, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3791_1]
                                            · have p3791_0 := h3791c.1
                                              have p3791_1 := h3791c.2.1
                                              have p3791_2 := h3791c.2.2.1
                                              have p3791_3 := h3791c.2.2.2
                                              linarith only [hlam, p3791_0]
                                  · linarith only [h3782, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  rcases p3779_3 (m.d 0 2) (by simp) with h3826 | h3826
                                  · rcases p3779_3 (m.d 1 2) (by simp) with h3827 | h3827
                                    · linarith only [h0, h3827, hlam]
                                    · rcases p3779_3 (m.d 2 3) (by simp) with h3829 | h3829
                                      · linarith only [h3829, h4, hlam]
                                      · linarith only [h3635, h3829, hlam]
                                  · linarith only [h3826, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  rcases p3779_3 (m.d 0 2) (by simp) with h3833 | h3833
                                  · rcases p3779_3 (m.d 1 2) (by simp) with h3834 | h3834
                                    · linarith only [h0, h3834, hlam]
                                    · rcases p3779_3 (m.d 2 3) (by simp) with h3836 | h3836
                                      · linarith only [h3836, h4, hlam]
                                      · linarith only [h3636, h3836, hlam]
                                  · linarith only [h3833, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h0, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h2520, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h3334, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h3619, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h4, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  rcases p3779_3 (m.d 0 2) (by simp) with h3846 | h3846
                                  · rcases p3779_3 (m.d 1 2) (by simp) with h3847 | h3847
                                    · linarith only [h3847, hlam, p3779_0]
                                    · rcases p3779_3 (m.d 2 3) (by simp) with h3849 | h3849
                                      · rcases p3779_3 (m.d 2 4) (by simp) with h3850 | h3850
                                        · linarith only [h3635, h3850, hlam]
                                        · linarith only [h3334, h3850, hlam]
                                      · linarith only [h3849, hlam, p3779_0]
                                  · linarith only [h0, h3846, hlam]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h0, h3334, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h0, h3619, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h5, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h0, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h3635, hlam, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h3637, hlam, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h6, hlam, p3779_0]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3641_1, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h3636, hlam, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3641_1, p3779_1]
                                · have p3779_0 := h3779c.1
                                  have p3779_1 := h3779c.2.1
                                  have p3779_2 := h3779c.2.2.1
                                  have p3779_3 := h3779c.2.2.2
                                  linarith only [hlam, p3779_0]
                          · linarith only [h3774, h8, hlam]
                        · linarith only [h3773, h6, hlam]
                      · linarith only [h3, h3772, hlam]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h2, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h5, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h7, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h9, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h3, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h6, hlam, p3641_1]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h8, hlam, p3641_0]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [h3334, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3641_1]
                    · have p3641_0 := h3641c.1
                      have p3641_1 := h3641c.2.1
                      have p3641_2 := h3641c.2.2.1
                      have p3641_3 := h3641c.2.2.2
                      linarith only [hlam, p3641_0]
              · linarith only [h2520, h3632, h3636, hlam]
            · linarith only [h2520, h3635, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3883 | h3883
          · linarith only [h2, h3883, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3885 | h3885
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3886 | h3886
              · linarith only [h0, h3631, h3632, h3886, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3888 | h3888
                · linarith only [h3885, h3886, h3888, h8, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3890 | h3890
                  · linarith only [h3334, h3631, h3885, h3886, h3890, h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h0bigk with h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c | h3892c
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3334, h3885, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3334, h3885, h3886, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      rcases p3892_3 (m.d 0 1) (by simp) with h3896 | h3896
                      · rcases p3892_3 (m.d 0 2) (by simp) with h3897 | h3897
                        · linarith only [h0, h3897, hlam]
                        · linarith only [h3897, h5, hlam]
                      · linarith only [h2, h3896, hlam]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3334, h3885, h3886, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h0, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3334, h3885, h3886, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      rcases p3892_3 (m.d 0 1) (by simp) with h3905 | h3905
                      · rcases p3892_3 (m.d 0 2) (by simp) with h3906 | h3906
                        · rcases p3892_3 (m.d 0 3) (by simp) with h3907 | h3907
                          · linarith only [h3907, h4, hlam]
                          · linarith only [h3907, h7, hlam]
                        · linarith only [h3906, h5, hlam]
                      · linarith only [h2, h3905, hlam]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h0, h3334, h3885, h3886, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h1, hlam, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h4, hlam, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      rcases p3892_3 (m.d 0 1) (by simp) with h3916 | h3916
                      · rcases p3892_3 (m.d 0 2) (by simp) with h3917 | h3917
                        · rcases p3892_3 (m.d 0 3) (by simp) with h3918 | h3918
                          · rcases p3892_3 (m.d 0 4) (by simp) with h3919 | h3919
                            · linarith only [h3919, h7, hlam]
                            · rcases p3892_3 (m.d 0 5) (by simp) with h3921 | h3921
                              · linarith only [h3921, h8, hlam]
                              · linarith only [h3921, h9, hlam]
                          · linarith only [h3918, h7, hlam]
                        · linarith only [h3917, h5, hlam]
                      · linarith only [h2, h3916, hlam]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3334, h3885, h3886, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h2, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h5, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h7, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h9, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h6, hlam, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h8, hlam, p3892_0]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [h3334, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3892_1]
                    · have p3892_0 := h3892c.1
                      have p3892_1 := h3892c.2.1
                      have p3892_2 := h3892c.2.2.1
                      have p3892_3 := h3892c.2.2.2
                      linarith only [hlam, p3892_0]
            · linarith only [h2520, h3631, h3885, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3939 | h3939
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3940 | h3940
          · linarith only [h3631, h3939, h3940, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3631, h3939, h3940, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3943 | h3943
          · linarith only [h2, h3631, h3943, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3945 | h3945
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3946 | h3946
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3947 | h3947
                · linarith only [h3947, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3949 | h3949
                  · linarith only [h3945, h3949, h5, h9, hlam]
                  · rcases h0bigk with h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c | h3951c
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h3939, h3943, h3946, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h2520, h3631, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      rcases p3951_3 (m.d 0 1) (by simp) with h3955 | h3955
                      · rcases p3951_3 (m.d 0 2) (by simp) with h3956 | h3956
                        · linarith only [h0, h3956, hlam]
                        · linarith only [h3956, h5, hlam]
                      · linarith only [h2, h3955, hlam]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      rcases p3951_3 (m.d 0 1) (by simp) with h3960 | h3960
                      · rcases p3951_3 (m.d 0 2) (by simp) with h3961 | h3961
                        · linarith only [h0, h3961, hlam]
                        · linarith only [h3961, h6, hlam]
                      · linarith only [h3, h3960, hlam]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h0, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h2520, h3631, h3946, h3949, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      rcases p3951_3 (m.d 0 1) (by simp) with h3968 | h3968
                      · rcases p3951_3 (m.d 0 2) (by simp) with h3969 | h3969
                        · rcases p3951_3 (m.d 0 3) (by simp) with h3970 | h3970
                          · linarith only [h3970, h4, hlam]
                          · linarith only [h3970, h7, hlam]
                        · linarith only [h3969, h5, hlam]
                      · linarith only [h2, h3968, hlam]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      rcases p3951_3 (m.d 0 1) (by simp) with h3975 | h3975
                      · rcases p3951_3 (m.d 0 2) (by simp) with h3976 | h3976
                        · rcases p3951_3 (m.d 0 3) (by simp) with h3977 | h3977
                          · linarith only [h3977, h4, hlam]
                          · linarith only [h3977, h8, hlam]
                        · linarith only [h3976, h6, hlam]
                      · linarith only [h3, h3975, hlam]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h1, hlam, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h4, hlam, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      rcases p3951_3 (m.d 0 1) (by simp) with h3985 | h3985
                      · rcases p3951_3 (m.d 0 2) (by simp) with h3986 | h3986
                        · rcases p3951_3 (m.d 0 3) (by simp) with h3987 | h3987
                          · rcases p3951_3 (m.d 0 4) (by simp) with h3988 | h3988
                            · linarith only [h3988, h7, hlam]
                            · rcases p3951_3 (m.d 0 5) (by simp) with h3990 | h3990
                              · linarith only [h3990, h8, hlam]
                              · linarith only [h3990, h9, hlam]
                          · linarith only [h3987, h7, hlam]
                        · linarith only [h3986, h5, hlam]
                      · linarith only [h2, h3985, hlam]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      rcases p3951_3 (m.d 0 1) (by simp) with h3996 | h3996
                      · rcases p3951_3 (m.d 0 2) (by simp) with h3997 | h3997
                        · rcases p3951_3 (m.d 0 3) (by simp) with h3998 | h3998
                          · rcases p3951_3 (m.d 0 4) (by simp) with h3999 | h3999
                            · linarith only [h3999, h7, hlam]
                            · rcases p3951_3 (m.d 0 5) (by simp) with h4001 | h4001
                              · linarith only [h4001, h8, hlam]
                              · rcases h2bigk with h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h2520, h3631, h3946, h3949, h4, hlam, p4003_2]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h2520, h3631, h3946, h3949, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  rcases p4003_3 (m.d 0 2) (by simp) with h4007 | h4007
                                  · rcases p4003_3 (m.d 1 2) (by simp) with h4008 | h4008
                                    · linarith only [h0, h4008, hlam]
                                    · rcases p4003_3 (m.d 2 3) (by simp) with h4010 | h4010
                                      · linarith only [h4, h4010, hlam]
                                      · linarith only [h3945, h4010, hlam]
                                  · linarith only [h4007, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  rcases p4003_3 (m.d 0 2) (by simp) with h4014 | h4014
                                  · rcases p4003_3 (m.d 1 2) (by simp) with h4015 | h4015
                                    · linarith only [h0, h4015, hlam]
                                    · rcases p4003_3 (m.d 2 3) (by simp) with h4017 | h4017
                                      · linarith only [h4, h4017, hlam]
                                      · linarith only [h3946, h4017, hlam]
                                  · linarith only [h4014, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h2520, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3334, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3619, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h4, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  rcases p4003_3 (m.d 0 2) (by simp) with h4027 | h4027
                                  · rcases p4003_3 (m.d 1 2) (by simp) with h4028 | h4028
                                    · linarith only [h4028, hlam, p4003_0]
                                    · rcases p4003_3 (m.d 2 3) (by simp) with h4030 | h4030
                                      · rcases p4003_3 (m.d 2 4) (by simp) with h4031 | h4031
                                        · linarith only [h3945, h4031, hlam]
                                        · linarith only [h3334, h4031, hlam]
                                      · linarith only [h4030, hlam, p4003_0]
                                  · linarith only [h0, h4027, hlam]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h2520, h3631, h3945, hc12, hc23, hlam, hphi, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, h2520, h3631, h3945, h3947, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h5, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3947, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3951_1, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3945, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3947, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h6, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3951_1, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3946, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3951_1, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                          · linarith only [h3998, h8, hlam]
                        · linarith only [h3997, h6, hlam]
                      · linarith only [h3, h3996, hlam]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h2, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h5, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h7, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h9, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h3, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h6, hlam, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h8, hlam, p3951_0]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [h2520, h3631, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3951_1]
                    · have p3951_0 := h3951c.1
                      have p3951_1 := h3951c.2.1
                      have p3951_2 := h3951c.2.2.1
                      have p3951_3 := h3951c.2.2.2
                      linarith only [hlam, p3951_0]
              · linarith only [h0, h2520, h3631, h3945, h3946, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h2520, h3945, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8110000 in
set_option maxHeartbeats 8110000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s8_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h2520 | h2520
  · exact r1l7_10_12_23_L_I_L_I_H_I_s8_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2520
  · exact r1l7_10_12_23_L_I_L_I_H_I_s8_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2520

set_option maxHeartbeats 8110000 in
set_option maxHeartbeats 8110000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s8 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_10_12_23_L_I_L_I_H_I_s8_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_10_12_23_L_I_L_I_H_I_s8_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

end R2N4
