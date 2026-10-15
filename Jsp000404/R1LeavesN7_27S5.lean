import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3336 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h3337 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h3338 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h3339 | h3339
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3340 | h3340
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3341 | h3341
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3342 | h3342
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3343 | h3343
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3344 | h3344
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3345 | h3345
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3346 | h3346
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3347 | h3347
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3348 | h3348
                    · linarith only [h3333, h3345, h3348, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h3333, h3345, h3347, h3348, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3351 | h3351
                    · linarith only [h3345, h3347, h3351, hlam]
                    · rcases h0bigk with h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h0, hlam, p3353_1]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h2914, hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3104, hlam, p3353_1]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3265, hlam, p3353_1]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        rcases p3353_3 (m.d 0 1) (by simp) with h3359 | h3359
                        · linarith only [h0, h3359, hlam]
                        · rcases p3353_3 (m.d 0 2) (by simp) with h3361 | h3361
                          · rcases p3353_3 (m.d 0 3) (by simp) with h3362 | h3362
                            · linarith only [h3333, h3362, hlam]
                            · linarith only [h2914, h3362, hlam]
                          · linarith only [h0, h3361, hlam]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h0, h3333, h3346, hc12, hlam, hphi, ht01, ht0b, ht5b, p3353_1, u5ehi3]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h0, h3338, h3345, h3347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1, u3ehi3]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h0, h3338, h3345, h3347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1, u3ehi3]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        rcases p3353_3 (m.d 0 1) (by simp) with h3370 | h3370
                        · linarith only [h2914, h3370, hlam]
                        · rcases p3353_3 (m.d 0 2) (by simp) with h3372 | h3372
                          · rcases p3353_3 (m.d 0 3) (by simp) with h3373 | h3373
                            · rcases p3353_3 (m.d 0 4) (by simp) with h3374 | h3374
                              · linarith only [h3336, h3374, hlam]
                              · linarith only [h3104, h3374, hlam]
                            · linarith only [h2914, h3373, hlam]
                          · linarith only [h0, h3372, hlam]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3333, hlam, p3353_1]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h2914, h3338, h3339, h3345, h3347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1, u3ehi3]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h2914, h3338, h3339, h3345, h3347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1, u3ehi3]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        rcases p3353_3 (m.d 0 1) (by simp) with h3383 | h3383
                        · linarith only [h3104, h3383, hlam]
                        · rcases p3353_3 (m.d 0 2) (by simp) with h3385 | h3385
                          · rcases p3353_3 (m.d 0 3) (by simp) with h3386 | h3386
                            · rcases p3353_3 (m.d 0 4) (by simp) with h3387 | h3387
                              · rcases p3353_3 (m.d 0 5) (by simp) with h3388 | h3388
                                · linarith only [h3338, h3388, hlam]
                                · linarith only [h3265, h3388, hlam]
                              · linarith only [h3104, h3387, hlam]
                            · linarith only [h2914, h3386, hlam]
                          · linarith only [h0, h3385, hlam]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3334, hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3336, hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3104, h3338, h3339, h3342, h3345, h3347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1, u3ehi3]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        rcases p3353_3 (m.d 0 1) (by simp) with h3398 | h3398
                        · linarith only [h3265, h3398, hlam]
                        · rcases p3353_3 (m.d 0 2) (by simp) with h3400 | h3400
                          · rcases p3353_3 (m.d 0 3) (by simp) with h3401 | h3401
                            · rcases p3353_3 (m.d 0 4) (by simp) with h3402 | h3402
                              · rcases p3353_3 (m.d 0 5) (by simp) with h3403 | h3403
                                · rcases h0emin with h3404 | h3404 | h3404 | h3404 | h3404
                                  · linarith only [h3104, h3338, h3339, h3342, h3404, hc12, hlam, ht01, p3353_1]
                                  · rcases h2bigk with h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h0, hlam, p3406_1]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h0, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3406_1, u3ehi3]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      rcases p3406_3 (m.d 0 2) (by simp) with h3410 | h3410
                                      · rcases p3406_3 (m.d 1 2) (by simp) with h3411 | h3411
                                        · rcases p3406_3 (m.d 2 3) (by simp) with h3412 | h3412
                                          · linarith only [h3333, h3412, hlam]
                                          · linarith only [h3345, h3412, hlam]
                                        · linarith only [h3340, h3411, hlam]
                                      · linarith only [h3410, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      rcases p3406_3 (m.d 0 2) (by simp) with h3417 | h3417
                                      · rcases p3406_3 (m.d 1 2) (by simp) with h3418 | h3418
                                        · rcases p3406_3 (m.d 2 3) (by simp) with h3419 | h3419
                                          · linarith only [h3333, h3419, hlam]
                                          · linarith only [h3346, h3419, hlam]
                                        · linarith only [h3341, h3418, hlam]
                                      · linarith only [h3417, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3404, hc12, hlam, ht01, p3406_1]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3406_1, u3ehi3]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      rcases p3406_3 (m.d 0 2) (by simp) with h3427 | h3427
                                      · linarith only [h0, h3427, hlam]
                                      · linarith only [h3334, h3427, hlam]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      rcases p3406_3 (m.d 0 2) (by simp) with h3430 | h3430
                                      · linarith only [h0, h3430, hlam]
                                      · linarith only [h3335, h3430, hlam]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3333, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3339, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3333, h3345, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3406_1, u3ehi3]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h0, h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3406_1, u3ehi3]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3334, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3340, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3345, hlam, p3406_1]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3347, hlam, p3406_1]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3335, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3341, hlam, p3406_0]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h3346, hlam, p3406_1]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [h0, h3335, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3406_1, u3ehi3]
                                    · have p3406_0 := h3406c.1
                                      have p3406_1 := h3406c.2.1
                                      have p3406_2 := h3406c.2.2.1
                                      have p3406_3 := h3406c.2.2.2
                                      linarith only [hlam, p3406_0]
                                  · rcases h2bigk with h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h0, hlam, p3448_1]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h0, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3448_1, u3ehi3]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      rcases p3448_3 (m.d 0 2) (by simp) with h3452 | h3452
                                      · rcases p3448_3 (m.d 1 2) (by simp) with h3453 | h3453
                                        · rcases p3448_3 (m.d 2 3) (by simp) with h3454 | h3454
                                          · linarith only [h3333, h3454, hlam]
                                          · linarith only [h3345, h3454, hlam]
                                        · linarith only [h3340, h3453, hlam]
                                      · linarith only [h3452, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      rcases p3448_3 (m.d 0 2) (by simp) with h3459 | h3459
                                      · rcases p3448_3 (m.d 1 2) (by simp) with h3460 | h3460
                                        · rcases p3448_3 (m.d 2 3) (by simp) with h3461 | h3461
                                          · linarith only [h3333, h3461, hlam]
                                          · linarith only [h3346, h3461, hlam]
                                        · linarith only [h3341, h3460, hlam]
                                      · linarith only [h3459, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3448_1, u3ehi3]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3448_1, u3ehi3]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      rcases p3448_3 (m.d 0 2) (by simp) with h3469 | h3469
                                      · linarith only [h0, h3469, hlam]
                                      · linarith only [h3334, h3469, hlam]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      rcases p3448_3 (m.d 0 2) (by simp) with h3472 | h3472
                                      · linarith only [h0, h3472, hlam]
                                      · linarith only [h3335, h3472, hlam]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3333, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3339, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3333, h3345, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3448_1, u3ehi3]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h0, h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3448_1, u3ehi3]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3334, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3340, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3345, hlam, p3448_1]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3347, hlam, p3448_1]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3335, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3341, hlam, p3448_0]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h3346, hlam, p3448_1]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [h0, h3335, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3448_1, u3ehi3]
                                    · have p3448_0 := h3448c.1
                                      have p3448_1 := h3448c.2.1
                                      have p3448_2 := h3448c.2.2.1
                                      have p3448_3 := h3448c.2.2.2
                                      linarith only [hlam, p3448_0]
                                  · rcases h2bigk with h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c | h3490c
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h0, hlam, p3490_1]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h0, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3490_1, u3ehi3]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      rcases p3490_3 (m.d 0 2) (by simp) with h3494 | h3494
                                      · rcases p3490_3 (m.d 1 2) (by simp) with h3495 | h3495
                                        · rcases p3490_3 (m.d 2 3) (by simp) with h3496 | h3496
                                          · linarith only [h3333, h3496, hlam]
                                          · linarith only [h3345, h3496, hlam]
                                        · linarith only [h3340, h3495, hlam]
                                      · linarith only [h3494, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      rcases p3490_3 (m.d 0 2) (by simp) with h3501 | h3501
                                      · rcases p3490_3 (m.d 1 2) (by simp) with h3502 | h3502
                                        · rcases p3490_3 (m.d 2 3) (by simp) with h3503 | h3503
                                          · linarith only [h3333, h3503, hlam]
                                          · linarith only [h3346, h3503, hlam]
                                        · linarith only [h3341, h3502, hlam]
                                      · linarith only [h3501, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3490_1, u3ehi3]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3490_1, u3ehi3]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      rcases p3490_3 (m.d 0 2) (by simp) with h3511 | h3511
                                      · linarith only [h0, h3511, hlam]
                                      · linarith only [h3334, h3511, hlam]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      rcases p3490_3 (m.d 0 2) (by simp) with h3514 | h3514
                                      · linarith only [h0, h3514, hlam]
                                      · linarith only [h3335, h3514, hlam]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3333, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3339, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3333, h3345, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3490_1, u3ehi3]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h0, h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3490_1, u3ehi3]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3334, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3340, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3345, hlam, p3490_1]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3347, hlam, p3490_1]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3335, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3341, hlam, p3490_0]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h3346, hlam, p3490_1]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [h0, h3335, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3490_1, u3ehi3]
                                    · have p3490_0 := h3490c.1
                                      have p3490_1 := h3490c.2.1
                                      have p3490_2 := h3490c.2.2.1
                                      have p3490_3 := h3490c.2.2.2
                                      linarith only [hlam, p3490_0]
                                  · rcases h2bigk with h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h0, hlam, p3532_1]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h0, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3532_1, u3ehi3]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      rcases p3532_3 (m.d 0 2) (by simp) with h3536 | h3536
                                      · rcases p3532_3 (m.d 1 2) (by simp) with h3537 | h3537
                                        · rcases p3532_3 (m.d 2 3) (by simp) with h3538 | h3538
                                          · linarith only [h3333, h3538, hlam]
                                          · linarith only [h3345, h3538, hlam]
                                        · linarith only [h3340, h3537, hlam]
                                      · linarith only [h3536, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      rcases p3532_3 (m.d 0 2) (by simp) with h3543 | h3543
                                      · rcases p3532_3 (m.d 1 2) (by simp) with h3544 | h3544
                                        · rcases p3532_3 (m.d 2 3) (by simp) with h3545 | h3545
                                          · linarith only [h3333, h3545, hlam]
                                          · linarith only [h3346, h3545, hlam]
                                        · linarith only [h3341, h3544, hlam]
                                      · linarith only [h3543, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3532_1, u3ehi3]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3532_1, u3ehi3]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      rcases p3532_3 (m.d 0 2) (by simp) with h3553 | h3553
                                      · linarith only [h0, h3553, hlam]
                                      · linarith only [h3334, h3553, hlam]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      rcases p3532_3 (m.d 0 2) (by simp) with h3556 | h3556
                                      · linarith only [h0, h3556, hlam]
                                      · linarith only [h3335, h3556, hlam]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3333, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3339, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3333, h3345, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3532_1, u3ehi3]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h0, h3333, h3346, h3351, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3532_1, u3ehi3]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3334, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3340, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3345, hlam, p3532_1]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3347, hlam, p3532_1]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3335, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3341, hlam, p3532_0]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h3346, hlam, p3532_1]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [h0, h3335, h3345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3532_1, u3ehi3]
                                    · have p3532_0 := h3532c.1
                                      have p3532_1 := h3532c.2.1
                                      have p3532_2 := h3532c.2.2.1
                                      have p3532_3 := h3532c.2.2.2
                                      linarith only [hlam, p3532_0]
                                · linarith only [h3265, h3403, hlam]
                              · linarith only [h3104, h3402, hlam]
                            · linarith only [h2914, h3401, hlam]
                          · linarith only [h0, h3400, hlam]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3335, hlam, p3353_1]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3337, hlam, p3353_0]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [h3338, hlam, p3353_1]
                      · have p3353_0 := h3353c.1
                        have p3353_1 := h3353c.2.1
                        have p3353_2 := h3353c.2.2.1
                        have p3353_3 := h3353c.2.2.2
                        linarith only [hlam, p3353_0]
                · linarith only [h2914, h3337, h3339, h3345, h3346, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3583 | h3583
                · linarith only [h3345, h3583, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3585 | h3585
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3586 | h3586
                    · rcases h0bigk with h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c | h3587c
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h0, hlam, p3587_1]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h2914, hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3104, hlam, p3587_1]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3265, hlam, p3587_1]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        rcases p3587_3 (m.d 0 1) (by simp) with h3593 | h3593
                        · linarith only [h0, h3593, hlam]
                        · rcases p3587_3 (m.d 0 2) (by simp) with h3595 | h3595
                          · rcases p3587_3 (m.d 0 3) (by simp) with h3596 | h3596
                            · linarith only [h3333, h3596, hlam]
                            · linarith only [h2914, h3596, hlam]
                          · linarith only [h0, h3595, hlam]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h0, h3336, h3583, h3586, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3587_1, u3ehi2]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h0, h3336, h3583, h3586, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3587_1, u3ehi2]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h0, h3337, h3583, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3587_1, u3ehi2]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        rcases p3587_3 (m.d 0 1) (by simp) with h3604 | h3604
                        · linarith only [h2914, h3604, hlam]
                        · rcases p3587_3 (m.d 0 2) (by simp) with h3606 | h3606
                          · rcases p3587_3 (m.d 0 3) (by simp) with h3607 | h3607
                            · rcases p3587_3 (m.d 0 4) (by simp) with h3608 | h3608
                              · linarith only [h3336, h3608, hlam]
                              · linarith only [h3104, h3608, hlam]
                            · linarith only [h2914, h3607, hlam]
                          · linarith only [h0, h3606, hlam]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3333, hlam, p3587_1]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3336, h3583, h3586, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3587_1, u3ehi2]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h2914, h3337, h3339, h3583, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3587_1, u3ehi2]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        rcases p3587_3 (m.d 0 1) (by simp) with h3617 | h3617
                        · linarith only [h3104, h3617, hlam]
                        · rcases p3587_3 (m.d 0 2) (by simp) with h3619 | h3619
                          · rcases p3587_3 (m.d 0 3) (by simp) with h3620 | h3620
                            · rcases p3587_3 (m.d 0 4) (by simp) with h3621 | h3621
                              · rcases p3587_3 (m.d 0 5) (by simp) with h3622 | h3622
                                · linarith only [h3338, h3622, hlam]
                                · linarith only [h3265, h3622, hlam]
                              · linarith only [h3104, h3621, hlam]
                            · linarith only [h2914, h3620, hlam]
                          · linarith only [h0, h3619, hlam]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3334, hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3336, hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3337, h3583, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p3587_1, u3ehi2]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        rcases p3587_3 (m.d 0 1) (by simp) with h3632 | h3632
                        · linarith only [h3265, h3632, hlam]
                        · rcases p3587_3 (m.d 0 2) (by simp) with h3634 | h3634
                          · rcases p3587_3 (m.d 0 3) (by simp) with h3635 | h3635
                            · rcases p3587_3 (m.d 0 4) (by simp) with h3636 | h3636
                              · rcases p3587_3 (m.d 0 5) (by simp) with h3637 | h3637
                                · rcases h0emin with h3638 | h3638 | h3638 | h3638 | h3638
                                  · linarith only [h3638, hc05, hlam, p3587_1]
                                  · rcases h2bigk with h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c | h3640c
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h0, hlam, p3640_1]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      rcases p3640_3 (m.d 0 2) (by simp) with h3643 | h3643
                                      · rcases p3640_3 (m.d 1 2) (by simp) with h3644 | h3644
                                        · rcases p3640_3 (m.d 2 3) (by simp) with h3645 | h3645
                                          · linarith only [h3645, hlam, p3640_0]
                                          · rcases p3640_3 (m.d 2 4) (by simp) with h3647 | h3647
                                            · linarith only [h3334, h3647, hlam]
                                            · linarith only [h3345, h3647, hlam]
                                        · linarith only [h3339, h3644, hlam]
                                      · linarith only [h3643, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h0, h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3640_1, u5ehi4]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      rcases p3640_3 (m.d 0 2) (by simp) with h3653 | h3653
                                      · rcases p3640_3 (m.d 1 2) (by simp) with h3654 | h3654
                                        · rcases p3640_3 (m.d 2 3) (by simp) with h3655 | h3655
                                          · linarith only [h3333, h3655, hlam]
                                          · rcases p3640_3 (m.d 2 4) (by simp) with h3657 | h3657
                                            · linarith only [h3334, h3657, hlam]
                                            · linarith only [h3585, h3657, hlam]
                                        · linarith only [h3341, h3654, hlam]
                                      · linarith only [h3653, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3638, hc12, hlam, ht01, p3640_1]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      rcases p3640_3 (m.d 0 2) (by simp) with h3664 | h3664
                                      · linarith only [h0, h3664, hlam]
                                      · linarith only [h3333, h3664, hlam]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3640_1, u5ehi4]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      rcases p3640_3 (m.d 0 2) (by simp) with h3668 | h3668
                                      · linarith only [h0, h3668, hlam]
                                      · linarith only [h3335, h3668, hlam]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3333, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3339, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3345, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3583, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3334, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3340, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3334, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3640_1, u3ehi2]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3345, h3583, hc34, hlam, hphi, p3640_1, u3ehi2]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3335, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3341, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h0, h3335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3640_1, u3ehi2]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [h3585, hlam, p3640_0]
                                    · have p3640_0 := h3640c.1
                                      have p3640_1 := h3640c.2.1
                                      have p3640_2 := h3640c.2.2.1
                                      have p3640_3 := h3640c.2.2.2
                                      linarith only [hlam, p3640_0]
                                  · rcases h2bigk with h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h0, hlam, p3686_1]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      rcases p3686_3 (m.d 0 2) (by simp) with h3689 | h3689
                                      · rcases p3686_3 (m.d 1 2) (by simp) with h3690 | h3690
                                        · rcases p3686_3 (m.d 2 3) (by simp) with h3691 | h3691
                                          · linarith only [h3691, hlam, p3686_0]
                                          · rcases p3686_3 (m.d 2 4) (by simp) with h3693 | h3693
                                            · linarith only [h3334, h3693, hlam]
                                            · linarith only [h3345, h3693, hlam]
                                        · linarith only [h3339, h3690, hlam]
                                      · linarith only [h3689, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h0, h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3686_1, u5ehi4]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      rcases p3686_3 (m.d 0 2) (by simp) with h3699 | h3699
                                      · rcases p3686_3 (m.d 1 2) (by simp) with h3700 | h3700
                                        · rcases p3686_3 (m.d 2 3) (by simp) with h3701 | h3701
                                          · linarith only [h3333, h3701, hlam]
                                          · rcases p3686_3 (m.d 2 4) (by simp) with h3703 | h3703
                                            · linarith only [h3334, h3703, hlam]
                                            · linarith only [h3585, h3703, hlam]
                                        · linarith only [h3341, h3700, hlam]
                                      · linarith only [h3699, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3333, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3686_1, u3ehi2]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      rcases p3686_3 (m.d 0 2) (by simp) with h3710 | h3710
                                      · linarith only [h0, h3710, hlam]
                                      · linarith only [h3333, h3710, hlam]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3686_1, u5ehi4]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      rcases p3686_3 (m.d 0 2) (by simp) with h3714 | h3714
                                      · linarith only [h0, h3714, hlam]
                                      · linarith only [h3335, h3714, hlam]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3333, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3339, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3345, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3583, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3334, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3340, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3334, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3686_1, u3ehi2]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h2914, h3336, h3339, h3345, h3583, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3686_1, u3ehi2]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3335, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3341, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h0, h3335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3686_1, u3ehi2]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [h3585, hlam, p3686_0]
                                    · have p3686_0 := h3686c.1
                                      have p3686_1 := h3686c.2.1
                                      have p3686_2 := h3686c.2.2.1
                                      have p3686_3 := h3686c.2.2.2
                                      linarith only [hlam, p3686_0]
                                  · rcases h2bigk with h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c | h3732c
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h0, hlam, p3732_1]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      rcases p3732_3 (m.d 0 2) (by simp) with h3735 | h3735
                                      · rcases p3732_3 (m.d 1 2) (by simp) with h3736 | h3736
                                        · rcases p3732_3 (m.d 2 3) (by simp) with h3737 | h3737
                                          · linarith only [h3737, hlam, p3732_0]
                                          · rcases p3732_3 (m.d 2 4) (by simp) with h3739 | h3739
                                            · linarith only [h3334, h3739, hlam]
                                            · linarith only [h3345, h3739, hlam]
                                        · linarith only [h3339, h3736, hlam]
                                      · linarith only [h3735, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h0, h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3732_1, u5ehi4]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      rcases p3732_3 (m.d 0 2) (by simp) with h3745 | h3745
                                      · rcases p3732_3 (m.d 1 2) (by simp) with h3746 | h3746
                                        · rcases p3732_3 (m.d 2 3) (by simp) with h3747 | h3747
                                          · linarith only [h3333, h3747, hlam]
                                          · rcases p3732_3 (m.d 2 4) (by simp) with h3749 | h3749
                                            · linarith only [h3334, h3749, hlam]
                                            · linarith only [h3585, h3749, hlam]
                                        · linarith only [h3341, h3746, hlam]
                                      · linarith only [h3745, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3333, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3732_1, u3ehi2]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      rcases p3732_3 (m.d 0 2) (by simp) with h3756 | h3756
                                      · linarith only [h0, h3756, hlam]
                                      · linarith only [h3333, h3756, hlam]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3732_1, u5ehi4]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      rcases p3732_3 (m.d 0 2) (by simp) with h3760 | h3760
                                      · linarith only [h0, h3760, hlam]
                                      · linarith only [h3335, h3760, hlam]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3333, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3339, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3345, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3583, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3334, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3340, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3334, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3732_1, u3ehi2]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h2914, h3336, h3339, h3345, h3583, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3732_1, u3ehi2]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3335, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3341, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h0, h3335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3732_1, u3ehi2]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [h3585, hlam, p3732_0]
                                    · have p3732_0 := h3732c.1
                                      have p3732_1 := h3732c.2.1
                                      have p3732_2 := h3732c.2.2.1
                                      have p3732_3 := h3732c.2.2.2
                                      linarith only [hlam, p3732_0]
                                  · rcases h2bigk with h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h0, hlam, p3778_1]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      rcases p3778_3 (m.d 0 2) (by simp) with h3781 | h3781
                                      · rcases p3778_3 (m.d 1 2) (by simp) with h3782 | h3782
                                        · rcases p3778_3 (m.d 2 3) (by simp) with h3783 | h3783
                                          · linarith only [h3783, hlam, p3778_0]
                                          · rcases p3778_3 (m.d 2 4) (by simp) with h3785 | h3785
                                            · linarith only [h3334, h3785, hlam]
                                            · linarith only [h3345, h3785, hlam]
                                        · linarith only [h3339, h3782, hlam]
                                      · linarith only [h3781, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h0, h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3778_1, u5ehi4]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      rcases p3778_3 (m.d 0 2) (by simp) with h3791 | h3791
                                      · rcases p3778_3 (m.d 1 2) (by simp) with h3792 | h3792
                                        · rcases p3778_3 (m.d 2 3) (by simp) with h3793 | h3793
                                          · linarith only [h3333, h3793, hlam]
                                          · rcases p3778_3 (m.d 2 4) (by simp) with h3795 | h3795
                                            · linarith only [h3334, h3795, hlam]
                                            · linarith only [h3585, h3795, hlam]
                                        · linarith only [h3341, h3792, hlam]
                                      · linarith only [h3791, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3333, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3778_1, u3ehi2]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      rcases p3778_3 (m.d 0 2) (by simp) with h3802 | h3802
                                      · linarith only [h0, h3802, hlam]
                                      · linarith only [h3333, h3802, hlam]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3585, hc12, hlam, hphi, ht01, ht0b, ht5b, p3778_1, u5ehi4]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      rcases p3778_3 (m.d 0 2) (by simp) with h3806 | h3806
                                      · linarith only [h0, h3806, hlam]
                                      · linarith only [h3335, h3806, hlam]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3333, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3339, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3345, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3583, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3334, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3340, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3334, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3778_1, u3ehi2]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h2914, h3336, h3339, h3345, h3583, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3778_1, u3ehi2]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3335, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3341, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h0, h3335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3778_1, u3ehi2]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [h3585, hlam, p3778_0]
                                    · have p3778_0 := h3778c.1
                                      have p3778_1 := h3778c.2.1
                                      have p3778_2 := h3778c.2.2.1
                                      have p3778_3 := h3778c.2.2.2
                                      linarith only [hlam, p3778_0]
                                · linarith only [h3265, h3637, hlam]
                              · linarith only [h3104, h3636, hlam]
                            · linarith only [h2914, h3635, hlam]
                          · linarith only [h0, h3634, hlam]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3335, hlam, p3587_1]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3337, hlam, p3587_0]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [h3338, hlam, p3587_1]
                      · have p3587_0 := h3587c.1
                        have p3587_1 := h3587c.2.1
                        have p3587_2 := h3587c.2.2.1
                        have p3587_3 := h3587c.2.2.2
                        linarith only [hlam, p3587_0]
                    · linarith only [h3104, h3338, h3339, h3342, h3345, h3586, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3833 | h3833
                    · linarith only [h2914, h3336, h3339, h3345, h3585, h3833, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h3104, h3338, h3339, h3342, h3345, h3833, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h3104, h3338, h3344, hlam]
          · linarith only [h2914, h3336, h3343, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2914, h3336, h3342, hlam]
      · linarith only [h0, h3335, h3341, hlam]
    · linarith only [h0, h3334, h3340, hlam]
  · linarith only [h0, h3333, h3339, hlam]

end R2N4
