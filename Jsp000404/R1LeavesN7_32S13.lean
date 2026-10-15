import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 0 4 5 (by decide) (by decide) with h3422 | h3422
  · linarith only [h2012, h2013, h3422, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3424 | h3424
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3425 | h3425
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3426 | h3426
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3427 | h3427
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3428 | h3428
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3429 | h3429
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3430 | h3430
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3431 | h3431
                  · linarith only [h0, h2009, h2013, h3431, h879, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3433 | h3433
                    · linarith only [h2010, h3422, h3433, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3435 | h3435
                      · linarith only [h2010, h3422, h3430, h3435, hc23, hlam, hphi, u2ehi3]
                      · rcases h2bigk with h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c | h3437c
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h0, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          rcases p3437_3 (m.d 0 2) (by simp) with h3440 | h3440
                          · rcases p3437_3 (m.d 1 2) (by simp) with h3441 | h3441
                            · rcases p3437_3 (m.d 2 3) (by simp) with h3442 | h3442
                              · linarith only [h3442, hlam, p3437_0]
                              · rcases p3437_3 (m.d 2 4) (by simp) with h3444 | h3444
                                · linarith only [h2010, h3444, hlam]
                                · rcases p3437_3 (m.d 2 5) (by simp) with h3446 | h3446
                                  · linarith only [h2011, h3446, hlam]
                                  · linarith only [h3431, h3446, hlam]
                            · linarith only [h3424, h3441, hlam]
                          · linarith only [h3440, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          rcases p3437_3 (m.d 0 2) (by simp) with h3451 | h3451
                          · rcases p3437_3 (m.d 1 2) (by simp) with h3452 | h3452
                            · rcases p3437_3 (m.d 2 3) (by simp) with h3453 | h3453
                              · linarith only [h2009, h3453, hlam]
                              · linarith only [h3430, h3453, hlam]
                            · linarith only [h3425, h3452, hlam]
                          · linarith only [h3451, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          rcases p3437_3 (m.d 0 2) (by simp) with h3458 | h3458
                          · rcases p3437_3 (m.d 1 2) (by simp) with h3459 | h3459
                            · rcases p3437_3 (m.d 2 3) (by simp) with h3460 | h3460
                              · linarith only [h2009, h3460, hlam]
                              · rcases p3437_3 (m.d 2 4) (by simp) with h3462 | h3462
                                · linarith only [h2010, h3462, hlam]
                                · rcases p3437_3 (m.d 2 5) (by simp) with h3464 | h3464
                                  · linarith only [h3464, hlam, p3437_0]
                                  · rcases h3bigk with h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h879, hlam, p3466_1]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2013, h3424, h3427, h3429, h3435, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3466_1, u2ehi2]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2013, h3424, h3427, h3429, h3435, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3466_1]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2013, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      rcases p3466_3 (m.d 0 3) (by simp) with h3472 | h3472
                                      · linarith only [h3472, h879, hlam]
                                      · rcases p3466_3 (m.d 1 3) (by simp) with h3474 | h3474
                                        · rcases p3466_3 (m.d 2 3) (by simp) with h3475 | h3475
                                          · linarith only [h3424, h3475, hlam]
                                          · rcases p3466_3 (m.d 3 4) (by simp) with h3477 | h3477
                                            · linarith only [h3427, h3477, hlam]
                                            · rcases p3466_3 (m.d 3 5) (by simp) with h3479 | h3479
                                              · linarith only [h3428, h3479, hlam]
                                              · linarith only [h2013, h3479, hlam]
                                        · linarith only [h3474, h879, hlam]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      rcases p3466_3 (m.d 0 3) (by simp) with h3484 | h3484
                                      · linarith only [h3484, h879, hlam]
                                      · linarith only [h2009, h3484, hlam]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2012, h2013, h3427, h3429, h3435, hlam, p3466_2]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2012, h2013, h3424, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3466_1]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2009, hlam, p3466_1]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3424, hlam, p3466_1]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2009, h2013, h3424, h3428, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3466_1]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3431, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2012, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3427, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3430, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3435, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h2009, hc35, hlam, hphi, ht23, p3466_1, u2ehi2]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3428, hlam, p3466_0]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [h3424, h3428, h3430, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3466_1, u2ehi3]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      rcases p3466_3 (m.d 0 3) (by simp) with h3502 | h3502
                                      · linarith only [h2013, h3502, hlam]
                                      · linarith only [h2012, h3502, hlam]
                                    · have p3466_0 := h3466c.1
                                      have p3466_1 := h3466c.2.1
                                      have p3466_2 := h3466c.2.2.1
                                      have p3466_3 := h3466c.2.2.2
                                      linarith only [hlam, p3466_0]
                            · linarith only [h3426, h3459, hlam]
                          · linarith only [h3458, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2009, h3430, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3437_1, u2ehi3]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          rcases p3437_3 (m.d 0 2) (by simp) with h3510 | h3510
                          · linarith only [h0, h3510, hlam]
                          · linarith only [h2009, h3510, hlam]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          rcases p3437_3 (m.d 0 2) (by simp) with h3513 | h3513
                          · linarith only [h0, h3513, hlam]
                          · linarith only [h2010, h3513, hlam]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          rcases p3437_3 (m.d 0 2) (by simp) with h3516 | h3516
                          · linarith only [h0, h3516, hlam]
                          · linarith only [h2011, h3516, hlam]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2009, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h3424, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2011, h3431, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3437_1, u2ehi3]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h3431, hlam, p3437_1]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2010, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h3425, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h3430, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h3433, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2011, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h3426, hlam, p3437_0]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2011, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3437_1, u2ehi2]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [h2011, h2013, h3424, h3427, h3429, h3435, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3437_1, u2ehi3]
                        · have p3437_0 := h3437c.1
                          have p3437_1 := h3437c.2.1
                          have p3437_2 := h3437c.2.2.1
                          have p3437_3 := h3437c.2.2.2
                          linarith only [hlam, p3437_0]
                · linarith only [h2012, h2013, h3430, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3535 | h3535
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3536 | h3536
                  · linarith only [h0, h2009, h2013, h3536, h879, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3538 | h3538
                    · linarith only [h2010, h2012, h2013, h3424, h3428, h3429, h3538, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3540 | h3540
                      · linarith only [h2009, h2013, h3428, h3429, h3535, h3540, hlam]
                      · rcases h2bigk with h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          rcases p3542_3 (m.d 0 2) (by simp) with h3545 | h3545
                          · rcases p3542_3 (m.d 1 2) (by simp) with h3546 | h3546
                            · rcases p3542_3 (m.d 2 3) (by simp) with h3547 | h3547
                              · linarith only [h3547, hlam, p3542_0]
                              · rcases p3542_3 (m.d 2 4) (by simp) with h3549 | h3549
                                · linarith only [h2010, h3549, hlam]
                                · rcases p3542_3 (m.d 2 5) (by simp) with h3551 | h3551
                                  · linarith only [h2011, h3551, hlam]
                                  · linarith only [h3536, h3551, hlam]
                            · linarith only [h3424, h3546, hlam]
                          · linarith only [h3545, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          rcases p3542_3 (m.d 0 2) (by simp) with h3556 | h3556
                          · rcases p3542_3 (m.d 1 2) (by simp) with h3557 | h3557
                            · rcases p3542_3 (m.d 2 3) (by simp) with h3558 | h3558
                              · linarith only [h2009, h3558, hlam]
                              · linarith only [h3535, h3558, hlam]
                            · linarith only [h3425, h3557, hlam]
                          · linarith only [h3556, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          rcases p3542_3 (m.d 0 2) (by simp) with h3563 | h3563
                          · rcases p3542_3 (m.d 1 2) (by simp) with h3564 | h3564
                            · rcases p3542_3 (m.d 2 3) (by simp) with h3565 | h3565
                              · linarith only [h2009, h3565, hlam]
                              · rcases p3542_3 (m.d 2 4) (by simp) with h3567 | h3567
                                · linarith only [h2010, h3567, hlam]
                                · rcases p3542_3 (m.d 2 5) (by simp) with h3569 | h3569
                                  · linarith only [h3569, hlam, p3542_0]
                                  · rcases h3bigk with h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h879, hlam, p3571_1]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2013, h3424, h3428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3571_1]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2013, h3424, h3428, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3571_1]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2013, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      rcases p3571_3 (m.d 0 3) (by simp) with h3577 | h3577
                                      · linarith only [h3577, h879, hlam]
                                      · rcases p3571_3 (m.d 1 3) (by simp) with h3579 | h3579
                                        · rcases p3571_3 (m.d 2 3) (by simp) with h3580 | h3580
                                          · linarith only [h3424, h3580, hlam]
                                          · rcases p3571_3 (m.d 3 4) (by simp) with h3582 | h3582
                                            · linarith only [h3427, h3582, hlam]
                                            · rcases p3571_3 (m.d 3 5) (by simp) with h3584 | h3584
                                              · linarith only [h3428, h3584, hlam]
                                              · linarith only [h2013, h3584, hlam]
                                        · linarith only [h3579, h879, hlam]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      rcases p3571_3 (m.d 0 3) (by simp) with h3589 | h3589
                                      · linarith only [h3589, h879, hlam]
                                      · linarith only [h2009, h3589, hlam]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2012, h2013, h3428, hlam, p3571_2]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2010, h2012, h2013, h3424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3571_1, u2ehi3]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2009, hlam, p3571_1]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3424, hlam, p3571_1]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2009, h2013, h3428, h3429, hc34, hc45, hlam, hphi, p3571_1]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3536, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2012, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3427, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3535, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3540, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h2009, h3428, h3429, hc45, hlam, hphi, ht23, ht34, p3571_1, u2ehi2]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3428, hlam, p3571_0]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [h3424, h3428, h3535, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3571_1, u2ehi3]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      rcases p3571_3 (m.d 0 3) (by simp) with h3607 | h3607
                                      · linarith only [h2013, h3607, hlam]
                                      · linarith only [h2012, h3607, hlam]
                                    · have p3571_0 := h3571c.1
                                      have p3571_1 := h3571c.2.1
                                      have p3571_2 := h3571c.2.2.1
                                      have p3571_3 := h3571c.2.2.2
                                      linarith only [hlam, p3571_0]
                            · linarith only [h3426, h3564, hlam]
                          · linarith only [h3563, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2009, h3535, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3542_1, u2ehi3]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          rcases p3542_3 (m.d 0 2) (by simp) with h3615 | h3615
                          · linarith only [h0, h3615, hlam]
                          · linarith only [h2009, h3615, hlam]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          rcases p3542_3 (m.d 0 2) (by simp) with h3618 | h3618
                          · linarith only [h0, h3618, hlam]
                          · linarith only [h2010, h3618, hlam]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          rcases p3542_3 (m.d 0 2) (by simp) with h3621 | h3621
                          · linarith only [h0, h3621, hlam]
                          · linarith only [h2011, h3621, hlam]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2009, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3424, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2011, h3536, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3542_1, u2ehi3]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3536, hlam, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2010, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3425, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3535, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3538, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2011, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3426, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2011, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3542_1, u2ehi2]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2011, h2013, h3424, h3428, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3542_1, u2ehi3]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                · linarith only [h2012, h2013, h3424, h3428, h3535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3640 | h3640
              · linarith only [h2011, h3422, h3427, h3428, h3640, hc35, hlam, hphi, ht23, u2ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3642 | h3642
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3643 | h3643
                  · linarith only [h3428, h3643, h879, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3645 | h3645
                    · linarith only [h1407, h2010, h2012, h2013, h3640, h3645, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3647 | h3647
                      · linarith only [h2010, h3422, h3647, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h2bigk with h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h0, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 2) (by simp) with h3652 | h3652
                          · rcases p3649_3 (m.d 1 2) (by simp) with h3653 | h3653
                            · rcases p3649_3 (m.d 2 3) (by simp) with h3654 | h3654
                              · linarith only [h3654, hlam, p3649_0]
                              · rcases p3649_3 (m.d 2 4) (by simp) with h3656 | h3656
                                · linarith only [h2010, h3656, hlam]
                                · rcases p3649_3 (m.d 2 5) (by simp) with h3658 | h3658
                                  · linarith only [h2011, h3658, hlam]
                                  · linarith only [h3643, h3658, hlam]
                            · linarith only [h3424, h3653, hlam]
                          · linarith only [h3652, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 2) (by simp) with h3663 | h3663
                          · rcases p3649_3 (m.d 1 2) (by simp) with h3664 | h3664
                            · rcases p3649_3 (m.d 2 3) (by simp) with h3665 | h3665
                              · linarith only [h2009, h3665, hlam]
                              · linarith only [h3642, h3665, hlam]
                            · linarith only [h3425, h3664, hlam]
                          · linarith only [h3663, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 2) (by simp) with h3670 | h3670
                          · rcases p3649_3 (m.d 1 2) (by simp) with h3671 | h3671
                            · rcases p3649_3 (m.d 2 3) (by simp) with h3672 | h3672
                              · linarith only [h2009, h3672, hlam]
                              · rcases p3649_3 (m.d 2 4) (by simp) with h3674 | h3674
                                · linarith only [h2010, h3674, hlam]
                                · rcases p3649_3 (m.d 2 5) (by simp) with h3676 | h3676
                                  · linarith only [h3676, hlam, p3649_0]
                                  · rcases h3bigk with h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c | h3678c
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h879, hlam, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3428, h3642, h3647, h879, hc45, hlam, hphi, ht23, ht34, p3678_1, u2ehi3]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3428, h3647, h879, hc34, hc45, hlam, hphi, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h2013, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3428, h3647, hc03, hc45, hlam, hphi, ht34, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3428, h3642, h3647, hc45, hlam, hphi, ht23, ht34, p3678_1, u2ehi3]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3428, h3647, hc34, hc45, hlam, hphi, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3428, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h2009, hlam, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3424, hlam, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h0, h3643, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3649_1, p3678_1]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3643, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h2012, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3427, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3642, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3647, hlam, p3678_0]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h2009, h3642, h3647, hc45, hlam, hphi, ht23, ht34, p3678_1, u2ehi3]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h0, h3642, h3643, h3647, h879, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3649_1, p3678_1, u2ehi3]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [h3642, h3647, hc45, hlam, hphi, ht23, ht34, p3678_1, u2ehi3]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      rcases p3678_3 (m.d 0 3) (by simp) with h3702 | h3702
                                      · linarith only [h2013, h3702, hlam]
                                      · linarith only [h2012, h3702, hlam]
                                    · have p3678_0 := h3678c.1
                                      have p3678_1 := h3678c.2.1
                                      have p3678_2 := h3678c.2.2.1
                                      have p3678_3 := h3678c.2.2.2
                                      linarith only [hlam, p3678_0]
                            · linarith only [h3426, h3671, hlam]
                          · linarith only [h3670, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2009, h3642, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3649_1, u2ehi3]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 2) (by simp) with h3710 | h3710
                          · linarith only [h0, h3710, hlam]
                          · linarith only [h2009, h3710, hlam]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 2) (by simp) with h3713 | h3713
                          · linarith only [h0, h3713, hlam]
                          · linarith only [h2010, h3713, hlam]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 2) (by simp) with h3716 | h3716
                          · linarith only [h0, h3716, hlam]
                          · linarith only [h2011, h3716, hlam]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2009, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3424, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2011, h3643, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3649_1, u2ehi3]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3643, hlam, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2010, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3425, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3642, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3645, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2011, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3426, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2011, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3649_1, u2ehi2]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h0, h2011, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3649_1, u2ehi3]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                · linarith only [h2012, h2013, h3642, hc23, hc35, hlam, hphi]
          · linarith only [h2012, h3427, h879, hlam]
        · linarith only [h0, h2011, h3426, hlam]
      · linarith only [h0, h2011, h3425, hc24, hlam, hphi, u2ehi4]
    · linarith only [h0, h2011, h3424, hc23, hlam, hphi, u2ehi4]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 0 3 5 (by decide) (by decide) with h2013 | h2013
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 0 3 5 (by decide) (by decide) with h3739 | h3739
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3740 | h3740
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3741 | h3741
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3742 | h3742
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3743 | h3743
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3744 | h3744
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3745 | h3745
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3746 | h3746
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3747 | h3747
                  · linarith only [h2009, h2011, h2012, h3739, h3747, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3749 | h3749
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3750 | h3750
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3751 | h3751
                        · rcases h2bigk with h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c | h3752c
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h0, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            rcases p3752_3 (m.d 0 2) (by simp) with h3755 | h3755
                            · rcases p3752_3 (m.d 1 2) (by simp) with h3756 | h3756
                              · rcases p3752_3 (m.d 2 3) (by simp) with h3757 | h3757
                                · linarith only [h3757, hlam, p3752_0]
                                · rcases p3752_3 (m.d 2 4) (by simp) with h3759 | h3759
                                  · linarith only [h2010, h3759, hlam]
                                  · linarith only [h3747, h3759, hlam]
                              · linarith only [h3741, h3756, hlam]
                            · linarith only [h3755, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            rcases p3752_3 (m.d 0 2) (by simp) with h3764 | h3764
                            · rcases p3752_3 (m.d 1 2) (by simp) with h3765 | h3765
                              · rcases p3752_3 (m.d 2 3) (by simp) with h3766 | h3766
                                · linarith only [h2009, h3766, hlam]
                                · rcases p3752_3 (m.d 2 4) (by simp) with h3768 | h3768
                                  · linarith only [h3768, hlam, p3752_0]
                                  · rcases p3752_3 (m.d 2 5) (by simp) with h3770 | h3770
                                    · linarith only [h2011, h3770, hlam]
                                    · rcases h3bigk with h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h879, hlam, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2012, h3741, h3744, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2012, hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2012, h3741, h3744, h3751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        rcases p3772_3 (m.d 0 3) (by simp) with h3778 | h3778
                                        · linarith only [h3778, h879, hlam]
                                        · rcases p3772_3 (m.d 1 3) (by simp) with h3780 | h3780
                                          · rcases p3772_3 (m.d 2 3) (by simp) with h3781 | h3781
                                            · linarith only [h3741, h3781, hlam]
                                            · rcases p3772_3 (m.d 3 4) (by simp) with h3783 | h3783
                                              · linarith only [h3744, h3783, hlam]
                                              · linarith only [h2012, h3783, hlam]
                                          · linarith only [h3780, h879, hlam]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        rcases p3772_3 (m.d 0 3) (by simp) with h3788 | h3788
                                        · linarith only [h3788, h879, hlam]
                                        · linarith only [h2009, h3788, hlam]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2012, h3741, h879, hc01, hc12, hlam, hphi, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2012, h3739, h3744, hlam, p3772_2]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2009, hlam, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3741, hlam, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3747, hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2009, h2012, h3744, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h2009, h3744, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3772_1, u2ehi2]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3744, hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3741, h3744, h3749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3772_1, u2ehi4]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        rcases p3772_3 (m.d 0 3) (by simp) with h3802 | h3802
                                        · linarith only [h2012, h3802, hlam]
                                        · linarith only [h3739, h3802, hlam]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3739, hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3745, hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3749, hlam, p3772_0]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [h3751, hlam, p3772_1]
                                      · have p3772_0 := h3772c.1
                                        have p3772_1 := h3772c.2.1
                                        have p3772_2 := h3772c.2.2.1
                                        have p3772_3 := h3772c.2.2.2
                                        linarith only [hlam, p3772_0]
                              · linarith only [h3742, h3765, hlam]
                            · linarith only [h3764, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            rcases p3752_3 (m.d 0 2) (by simp) with h3812 | h3812
                            · rcases p3752_3 (m.d 1 2) (by simp) with h3813 | h3813
                              · rcases p3752_3 (m.d 2 3) (by simp) with h3814 | h3814
                                · linarith only [h2009, h3814, hlam]
                                · linarith only [h3749, h3814, hlam]
                              · linarith only [h3743, h3813, hlam]
                            · linarith only [h3812, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2009, h3749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3752_1, u2ehi4]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            rcases p3752_3 (m.d 0 2) (by simp) with h3821 | h3821
                            · linarith only [h0, h3821, hlam]
                            · linarith only [h2009, h3821, hlam]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            rcases p3752_3 (m.d 0 2) (by simp) with h3824 | h3824
                            · linarith only [h0, h3824, hlam]
                            · linarith only [h2010, h3824, hlam]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            rcases p3752_3 (m.d 0 2) (by simp) with h3827 | h3827
                            · linarith only [h0, h3827, hlam]
                            · linarith only [h2011, h3827, hlam]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2009, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h3741, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h3747, hlam, p3752_1]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2010, h3747, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3752_1, u2ehi4]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2010, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h3742, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2010, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3752_1, u2ehi2]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2010, h2012, h3741, h3744, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3752_1, u2ehi4]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h2011, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h3743, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h3749, hlam, p3752_0]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [h3750, hlam, p3752_1]
                          · have p3752_0 := h3752c.1
                            have p3752_1 := h3752c.2.1
                            have p3752_2 := h3752c.2.2.1
                            have p3752_3 := h3752c.2.2.2
                            linarith only [hlam, p3752_0]
                        · linarith only [h2011, h2012, h3739, h3751, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · linarith only [h2012, h3739, h3740, h3750, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h2012, h3739, h3741, h3744, h3749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h2012, h3739, h3740, h3744, h3746, hlam]
              · linarith only [h2012, h3739, h3744, h3745, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3850 | h3850
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3851 | h3851
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3852 | h3852
                  · linarith only [h2009, h3744, h3852, h879, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3854 | h3854
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3855 | h3855
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3856 | h3856
                        · rcases h2bigk with h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c | h3857c
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h0, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            rcases p3857_3 (m.d 0 2) (by simp) with h3860 | h3860
                            · rcases p3857_3 (m.d 1 2) (by simp) with h3861 | h3861
                              · rcases p3857_3 (m.d 2 3) (by simp) with h3862 | h3862
                                · linarith only [h3862, hlam, p3857_0]
                                · rcases p3857_3 (m.d 2 4) (by simp) with h3864 | h3864
                                  · linarith only [h2010, h3864, hlam]
                                  · linarith only [h3852, h3864, hlam]
                              · linarith only [h3741, h3861, hlam]
                            · linarith only [h3860, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            rcases p3857_3 (m.d 0 2) (by simp) with h3869 | h3869
                            · rcases p3857_3 (m.d 1 2) (by simp) with h3870 | h3870
                              · rcases p3857_3 (m.d 2 3) (by simp) with h3871 | h3871
                                · linarith only [h2009, h3871, hlam]
                                · rcases p3857_3 (m.d 2 4) (by simp) with h3873 | h3873
                                  · linarith only [h3873, hlam, p3857_0]
                                  · rcases p3857_3 (m.d 2 5) (by simp) with h3875 | h3875
                                    · linarith only [h2011, h3875, hlam]
                                    · rcases h3bigk with h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c | h3877c
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h879, hlam, p3877_1]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h2012, hc34, hlam, hphi, ht23, p3877_1, u2ehi2]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h2012, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        rcases p3877_3 (m.d 0 3) (by simp) with h3882 | h3882
                                        · rcases p3877_3 (m.d 1 3) (by simp) with h3883 | h3883
                                          · rcases p3877_3 (m.d 2 3) (by simp) with h3884 | h3884
                                            · linarith only [h2009, h3884, hlam]
                                            · linarith only [h3854, h3884, hlam]
                                          · linarith only [h3850, h3883, hlam]
                                        · linarith only [h3882, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3744, hc03, hc34, hlam, hphi, p3877_1]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3744, h3854, hc34, hlam, hphi, ht23, p3877_1, u2ehi4]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3744, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        rcases p3877_3 (m.d 0 3) (by simp) with h3893 | h3893
                                        · linarith only [h3893, h879, hlam]
                                        · linarith only [h3739, h3893, hlam]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h2009, hlam, p3877_1]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3741, hlam, p3877_1]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3852, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h0, h3852, h3856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3857_1, p3877_1]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h2009, h3854, hc34, hlam, hphi, ht23, p3877_1, u2ehi4]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h0, h3852, h3854, h879, hc01, hc12, hc34, hlam, hphi, ht23, p3857_1, p3877_1, u2ehi4]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3854, hc34, hlam, hphi, ht23, p3877_1, u2ehi4]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        rcases p3877_3 (m.d 0 3) (by simp) with h3905 | h3905
                                        · linarith only [h2012, h3905, hlam]
                                        · linarith only [h3739, h3905, hlam]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3739, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3850, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3854, hlam, p3877_0]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [h3856, hlam, p3877_1]
                                      · have p3877_0 := h3877c.1
                                        have p3877_1 := h3877c.2.1
                                        have p3877_2 := h3877c.2.2.1
                                        have p3877_3 := h3877c.2.2.2
                                        linarith only [hlam, p3877_0]
                              · linarith only [h3742, h3870, hlam]
                            · linarith only [h3869, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            rcases p3857_3 (m.d 0 2) (by simp) with h3915 | h3915
                            · rcases p3857_3 (m.d 1 2) (by simp) with h3916 | h3916
                              · rcases p3857_3 (m.d 2 3) (by simp) with h3917 | h3917
                                · linarith only [h2009, h3917, hlam]
                                · linarith only [h3854, h3917, hlam]
                              · linarith only [h3743, h3916, hlam]
                            · linarith only [h3915, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h2009, h3854, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3857_1, u2ehi4]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            rcases p3857_3 (m.d 0 2) (by simp) with h3924 | h3924
                            · linarith only [h0, h3924, hlam]
                            · linarith only [h2009, h3924, hlam]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            rcases p3857_3 (m.d 0 2) (by simp) with h3927 | h3927
                            · linarith only [h0, h3927, hlam]
                            · linarith only [h2010, h3927, hlam]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            rcases p3857_3 (m.d 0 2) (by simp) with h3930 | h3930
                            · linarith only [h0, h3930, hlam]
                            · linarith only [h2011, h3930, hlam]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h2009, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h3741, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h3852, hlam, p3857_1]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h2010, h3852, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3857_1, u2ehi4]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h2010, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h3742, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h2010, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3857_1, u2ehi2]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h0, h2010, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3857_1, u2ehi4]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h2011, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h3743, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h3854, hlam, p3857_0]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [h3855, hlam, p3857_1]
                          · have p3857_0 := h3857c.1
                            have p3857_1 := h3857c.2.1
                            have p3857_2 := h3857c.2.2.1
                            have p3857_3 := h3857c.2.2.2
                            linarith only [hlam, p3857_0]
                        · linarith only [h2011, h2012, h3739, h3856, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · linarith only [h2012, h3740, h3855, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h2012, h3739, h3854, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h3739, h3740, h3742, h3744, h3851, h879, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h3739, h3850, h879, hlam]
          · linarith only [h0, h2009, h3743, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h2009, h3742, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h2009, h3741, hlam]
    · linarith only [h2012, h3739, h3740, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3957 | h3957
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3958 | h3958
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3959 | h3959
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3960 | h3960
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3961 | h3961
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3962 | h3962
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3963 | h3963
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3964 | h3964
                  · linarith only [h2009, h2012, h3964, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3966 | h3966
                    · linarith only [h2009, h3739, h3966, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3968 | h3968
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3969 | h3969
                        · rcases h2bigk with h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h0, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            rcases p3970_3 (m.d 0 2) (by simp) with h3973 | h3973
                            · rcases p3970_3 (m.d 1 2) (by simp) with h3974 | h3974
                              · rcases p3970_3 (m.d 2 3) (by simp) with h3975 | h3975
                                · linarith only [h3975, hlam, p3970_0]
                                · rcases p3970_3 (m.d 2 4) (by simp) with h3977 | h3977
                                  · linarith only [h2010, h3977, hlam]
                                  · linarith only [h3964, h3977, hlam]
                              · linarith only [h3958, h3974, hlam]
                            · linarith only [h3973, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            rcases p3970_3 (m.d 0 2) (by simp) with h3982 | h3982
                            · rcases p3970_3 (m.d 1 2) (by simp) with h3983 | h3983
                              · rcases p3970_3 (m.d 2 3) (by simp) with h3984 | h3984
                                · linarith only [h2009, h3984, hlam]
                                · rcases p3970_3 (m.d 2 4) (by simp) with h3986 | h3986
                                  · linarith only [h3986, hlam, p3970_0]
                                  · rcases p3970_3 (m.d 2 5) (by simp) with h3988 | h3988
                                    · linarith only [h2011, h3988, hlam]
                                    · rcases h3bigk with h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c | h3990c
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h879, hlam, p3990_1]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3739, h3958, h3961, h3969, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h2012, hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3739, hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        rcases p3990_3 (m.d 0 3) (by simp) with h3996 | h3996
                                        · linarith only [h3996, h879, hlam]
                                        · rcases p3990_3 (m.d 1 3) (by simp) with h3998 | h3998
                                          · rcases p3990_3 (m.d 2 3) (by simp) with h3999 | h3999
                                            · linarith only [h3958, h3999, hlam]
                                            · rcases p3990_3 (m.d 3 4) (by simp) with h4001 | h4001
                                              · linarith only [h3961, h4001, hlam]
                                              · linarith only [h2012, h4001, hlam]
                                          · linarith only [h3998, h879, hlam]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        rcases p3990_3 (m.d 0 3) (by simp) with h4006 | h4006
                                        · linarith only [h4006, h879, hlam]
                                        · linarith only [h2009, h4006, hlam]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3739, h3958, h3969, h879, hc01, hc12, hlam, hphi, p3990_1]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h2009, h3739, h3958, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h2009, hlam, p3990_1]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3958, hlam, p3990_1]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3964, hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3966, hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h2009, hc34, hlam, hphi, ht23, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3961, hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3958, h3961, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h2009, h3739, h3958, h3961, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h2009, hc35, hlam, hphi, ht23, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3962, hlam, p3990_0]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3958, h3962, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3990_1, u2ehi2]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [h3969, hlam, p3990_1]
                                      · have p3990_0 := h3990c.1
                                        have p3990_1 := h3990c.2.1
                                        have p3990_2 := h3990c.2.2.1
                                        have p3990_3 := h3990c.2.2.2
                                        linarith only [hlam, p3990_0]
                              · linarith only [h3959, h3983, hlam]
                            · linarith only [h3982, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            rcases p3970_3 (m.d 0 2) (by simp) with h4028 | h4028
                            · rcases p3970_3 (m.d 1 2) (by simp) with h4029 | h4029
                              · rcases p3970_3 (m.d 2 3) (by simp) with h4030 | h4030
                                · linarith only [h2009, h4030, hlam]
                                · rcases p3970_3 (m.d 2 4) (by simp) with h4032 | h4032
                                  · linarith only [h2010, h4032, hlam]
                                  · linarith only [h3968, h4032, hlam]
                              · linarith only [h3960, h4029, hlam]
                            · linarith only [h4028, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3970_1, u2ehi2]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            rcases p3970_3 (m.d 0 2) (by simp) with h4039 | h4039
                            · linarith only [h0, h4039, hlam]
                            · linarith only [h2009, h4039, hlam]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            rcases p3970_3 (m.d 0 2) (by simp) with h4042 | h4042
                            · linarith only [h0, h4042, hlam]
                            · linarith only [h2010, h4042, hlam]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            rcases p3970_3 (m.d 0 2) (by simp) with h4045 | h4045
                            · linarith only [h0, h4045, hlam]
                            · linarith only [h2011, h4045, hlam]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h2009, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h3958, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h3964, hlam, p3970_1]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h3966, hlam, p3970_1]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h2010, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h3959, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h2010, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3970_1, u2ehi2]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h2010, h2012, h3958, h3961, h3966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3970_1, u2ehi2]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h2011, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h3960, hlam, p3970_0]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [hc25, hlam, hphi, p3970_1, u2ehi2]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [h3968, hlam, p3970_1]
                          · have p3970_0 := h3970c.1
                            have p3970_1 := h3970c.2.1
                            have p3970_2 := h3970c.2.2.1
                            have p3970_3 := h3970c.2.2.2
                            linarith only [hlam, p3970_0]
                        · linarith only [h2009, h2012, h3968, h3969, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h2012, h3957, h3958, h3961, h3964, h3968, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h2012, h3957, h3961, h3963, hlam]
              · linarith only [h2011, h2012, h3957, h3961, h3962, hc35, hlam, hphi, ht23, u2ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4067 | h4067
              · linarith only [h2009, h3739, h3961, h4067, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4069 | h4069
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4070 | h4070
                  · linarith only [h3961, h4070, h879, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4072 | h4072
                    · linarith only [h4067, h4070, h4072, h879, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4074 | h4074
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4075 | h4075
                        · rcases h2bigk with h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h0, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            rcases p4076_3 (m.d 0 2) (by simp) with h4079 | h4079
                            · rcases p4076_3 (m.d 1 2) (by simp) with h4080 | h4080
                              · rcases p4076_3 (m.d 2 3) (by simp) with h4081 | h4081
                                · linarith only [h4081, hlam, p4076_0]
                                · rcases p4076_3 (m.d 2 4) (by simp) with h4083 | h4083
                                  · linarith only [h2010, h4083, hlam]
                                  · linarith only [h4070, h4083, hlam]
                              · linarith only [h3958, h4080, hlam]
                            · linarith only [h4079, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            rcases p4076_3 (m.d 0 2) (by simp) with h4088 | h4088
                            · rcases p4076_3 (m.d 1 2) (by simp) with h4089 | h4089
                              · rcases p4076_3 (m.d 2 3) (by simp) with h4090 | h4090
                                · linarith only [h2009, h4090, hlam]
                                · rcases p4076_3 (m.d 2 4) (by simp) with h4092 | h4092
                                  · linarith only [h4092, hlam, p4076_0]
                                  · rcases p4076_3 (m.d 2 5) (by simp) with h4094 | h4094
                                    · linarith only [h2011, h4094, hlam]
                                    · rcases h3bigk with h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c | h4096c
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h879, hlam, p4096_1]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4067, h4075, h879, hc34, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h2012, hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h3739, hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4067, h4075, hc03, hc34, hlam, hphi, p4096_1]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4067, h4075, hc34, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h3961, hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4067, hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h2009, hlam, p4096_1]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h3958, hlam, p4096_1]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4070, hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4072, hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h2009, hc34, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h0, h879, hc01, hc12, hc34, hlam, hphi, ht23, p4076_1, p4096_1, u2ehi3]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hc34, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hlam, p4096_0]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h2009, h3739, hc34, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h2009, hc35, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h0, h879, hc01, hc12, hc35, hlam, hphi, ht23, p4076_1, p4096_1, u2ehi3]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht23, p4096_1, u2ehi2]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [h4075, hlam, p4096_1]
                                      · have p4096_0 := h4096c.1
                                        have p4096_1 := h4096c.2.1
                                        have p4096_2 := h4096c.2.2.1
                                        have p4096_3 := h4096c.2.2.2
                                        linarith only [hlam, p4096_0]
                              · linarith only [h3959, h4089, hlam]
                            · linarith only [h4088, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            rcases p4076_3 (m.d 0 2) (by simp) with h4124 | h4124
                            · rcases p4076_3 (m.d 1 2) (by simp) with h4125 | h4125
                              · rcases p4076_3 (m.d 2 3) (by simp) with h4126 | h4126
                                · linarith only [h2009, h4126, hlam]
                                · rcases p4076_3 (m.d 2 4) (by simp) with h4128 | h4128
                                  · linarith only [h2010, h4128, hlam]
                                  · linarith only [h4074, h4128, hlam]
                              · linarith only [h3960, h4125, hlam]
                            · linarith only [h4124, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4076_1, u2ehi2]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            rcases p4076_3 (m.d 0 2) (by simp) with h4135 | h4135
                            · linarith only [h0, h4135, hlam]
                            · linarith only [h2009, h4135, hlam]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            rcases p4076_3 (m.d 0 2) (by simp) with h4138 | h4138
                            · linarith only [h0, h4138, hlam]
                            · linarith only [h2010, h4138, hlam]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            rcases p4076_3 (m.d 0 2) (by simp) with h4141 | h4141
                            · linarith only [h0, h4141, hlam]
                            · linarith only [h2011, h4141, hlam]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h2009, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h3958, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h4070, hlam, p4076_1]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h4072, hlam, p4076_1]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h2010, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h3959, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h2010, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4076_1, u2ehi2]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h0, h2010, h4072, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4076_1, u2ehi2]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h2011, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h3960, hlam, p4076_0]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [hc25, hlam, hphi, p4076_1, u2ehi2]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [h4074, hlam, p4076_1]
                          · have p4076_0 := h4076c.1
                            have p4076_1 := h4076c.2.1
                            have p4076_2 := h4076c.2.2.1
                            have p4076_3 := h4076c.2.2.2
                            linarith only [hlam, p4076_0]
                        · linarith only [h0, h2009, h2010, h2012, h4074, h4075, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h2012, h3957, h4074, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h2012, h3957, h3959, h4069, hc34, hlam, hphi, ht23, u2ehi3]
          · linarith only [h0, h2009, h3960, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h2011, h3959, hc24, hlam, hphi, u2ehi4]
      · linarith only [h0, h2011, h3958, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4165 | h4165
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4166 | h4166
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4167 | h4167
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4168 | h4168
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4169 | h4169
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4170 | h4170
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4171 | h4171
                  · linarith only [h2009, h2012, h4171, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4173 | h4173
                    · linarith only [h2009, h3739, h4173, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4175 | h4175
                      · linarith only [h2010, h3957, h4175, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4177 | h4177
                        · linarith only [h2009, h2012, h3957, h4177, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h2009, h2012, h4165, h4168, h4170, h4177, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h2009, h2012, h4168, h4170, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h2009, h2012, h4168, h4169, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4182 | h4182
              · linarith only [h2009, h3739, h4168, h4182, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4184 | h4184
                · linarith only [h2010, h3957, h4168, h4184, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4186 | h4186
                  · linarith only [h2009, h2012, h4186, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4188 | h4188
                    · linarith only [h2009, h3739, h4188, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4190 | h4190
                      · linarith only [h4168, h4184, h4190, h879, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4192 | h4192
                        · linarith only [h2009, h4168, h4184, h4192, h879, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h2009, h2012, h4192, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h2009, h4167, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h2010, h4166, hlam]
      · linarith only [h0, h2009, h4165, hlam]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 0 3 4 (by decide) (by decide) with h2012 | h2012
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012

end R2N4
