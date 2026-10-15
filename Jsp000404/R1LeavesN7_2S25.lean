import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S23
import Jsp000404.R1LeavesN7_2S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14402 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h14861 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h15018 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 1 2 3 (by decide) (by decide) with h15420 | h15420
  · rcases m.htr 1 2 4 (by decide) (by decide) with h15421 | h15421
    · rcases m.htr 1 2 5 (by decide) (by decide) with h15422 | h15422
      · rcases m.htr 1 3 4 (by decide) (by decide) with h15423 | h15423
        · linarith only [h14396, h14402, h15423, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15425 | h15425
          · linarith only [h14396, h14861, h15425, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15427 | h15427
            · linarith only [h0, h14397, h15018, h15427, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15429 | h15429
              · linarith only [h14396, h14402, h15420, h15429, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15431 | h15431
                · linarith only [h14396, h14861, h15420, h15431, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15433 | h15433
                  · linarith only [h14397, h15018, h15421, h15433, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15435 | h15435
                    · rcases h0bigk with h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c | h15436c
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h0, hlam, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15439 | h15439
                        · rcases p15436_3 (m.d 0 2) (by simp) with h15440 | h15440
                          · rcases p15436_3 (m.d 0 3) (by simp) with h15441 | h15441
                            · linarith only [h14396, h15441, hlam]
                            · rcases p15436_3 (m.d 0 4) (by simp) with h15443 | h15443
                              · linarith only [h14397, h15443, hlam]
                              · linarith only [h14402, h15443, hlam]
                          · linarith only [h14399, h15440, hlam]
                        · linarith only [h14396, h15439, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15448 | h15448
                        · rcases p15436_3 (m.d 0 2) (by simp) with h15449 | h15449
                          · rcases p15436_3 (m.d 0 3) (by simp) with h15450 | h15450
                            · linarith only [h14396, h15450, hlam]
                            · rcases p15436_3 (m.d 0 4) (by simp) with h15452 | h15452
                              · linarith only [h14397, h15452, hlam]
                              · rcases p15436_3 (m.d 0 5) (by simp) with h15454 | h15454
                                · linarith only [h14398, h15454, hlam]
                                · linarith only [h15018, h15454, hlam]
                          · linarith only [h14400, h15449, hlam]
                        · linarith only [h14397, h15448, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15459 | h15459
                        · rcases p15436_3 (m.d 0 2) (by simp) with h15460 | h15460
                          · rcases p15436_3 (m.d 0 3) (by simp) with h15461 | h15461
                            · linarith only [h14396, h15461, hlam]
                            · rcases p15436_3 (m.d 0 4) (by simp) with h15463 | h15463
                              · linarith only [h14397, h15463, hlam]
                              · rcases p15436_3 (m.d 0 5) (by simp) with h15465 | h15465
                                · linarith only [h14398, h15465, hlam]
                                · rcases h2bigk with h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c | h15467c
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, hlam, p15467_1]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    rcases p15467_3 (m.d 0 2) (by simp) with h15470 | h15470
                                    · rcases p15467_3 (m.d 1 2) (by simp) with h15471 | h15471
                                      · rcases p15467_3 (m.d 2 3) (by simp) with h15472 | h15472
                                        · linarith only [h15472, hlam, p15467_0]
                                        · rcases p15467_3 (m.d 2 4) (by simp) with h15474 | h15474
                                          · linarith only [h14400, h15474, hlam]
                                          · linarith only [h15429, h15474, hlam]
                                      · linarith only [h15420, h15471, hlam]
                                    · linarith only [h15470, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    rcases p15467_3 (m.d 0 2) (by simp) with h15479 | h15479
                                    · rcases p15467_3 (m.d 1 2) (by simp) with h15480 | h15480
                                      · rcases p15467_3 (m.d 2 3) (by simp) with h15481 | h15481
                                        · linarith only [h14399, h15481, hlam]
                                        · rcases p15467_3 (m.d 2 4) (by simp) with h15483 | h15483
                                          · linarith only [h15483, hlam, p15467_0]
                                          · rcases p15467_3 (m.d 2 5) (by simp) with h15485 | h15485
                                            · linarith only [h14401, h15485, hlam]
                                            · linarith only [h15433, h15485, hlam]
                                      · linarith only [h15421, h15480, hlam]
                                    · linarith only [h15479, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    rcases p15467_3 (m.d 0 2) (by simp) with h15490 | h15490
                                    · rcases p15467_3 (m.d 1 2) (by simp) with h15491 | h15491
                                      · rcases p15467_3 (m.d 2 3) (by simp) with h15492 | h15492
                                        · linarith only [h14399, h15492, hlam]
                                        · rcases p15467_3 (m.d 2 4) (by simp) with h15494 | h15494
                                          · linarith only [h14400, h15494, hlam]
                                          · rcases p15467_3 (m.d 2 5) (by simp) with h15496 | h15496
                                            · linarith only [h15496, hlam, p15467_0]
                                            · rcases h3bigk with h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c | h15498c
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h0, h14396, h15420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h0, h14396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h14402, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h14861, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h14396, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h0, h14396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15423, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15425, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h14399, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15420, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15429, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15431, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hc13, hc34, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h14402, h15018, h15435, hc03, hc34, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h14396, h15420, hc23, hc35, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15420, hc23, hc35, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p15498_1]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [h15435, hlam, p15498_0]
                                              · have p15498_0 := h15498c.1
                                                have p15498_1 := h15498c.2.1
                                                have p15498_2 := h15498c.2.2.1
                                                have p15498_3 := h15498c.2.2.2
                                                linarith only [hlam, p15498_0]
                                      · linarith only [h15422, h15491, hlam]
                                    · linarith only [h15490, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, h14396, h14402, h15018, h15420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15436_1, p15467_1]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, h14396, h14402, h15018, h15420, hlam, p15436_1, p15467_2]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, h14397, h15018, h15421, hlam, p15436_1, p15467_2]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, h14398, h15422, hlam, p15436_1, p15467_2]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h14399, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h15420, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h15429, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h15431, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h14400, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h15421, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h14397, h15018, h15421, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15436_1, p15467_1]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h15433, hlam, p15467_1]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h14401, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h15422, hlam, p15467_0]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15436_1, p15467_1]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15436_1, p15467_1]
                                  · have p15467_0 := h15467c.1
                                    have p15467_1 := h15467c.2.1
                                    have p15467_2 := h15467c.2.2.1
                                    have p15467_3 := h15467c.2.2.2
                                    linarith only [hlam, p15467_0]
                          · linarith only [h14401, h15460, hlam]
                        · linarith only [h14398, h15459, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15548 | h15548
                        · linarith only [h0, h15548, hlam]
                        · rcases p15436_3 (m.d 0 2) (by simp) with h15550 | h15550
                          · rcases p15436_3 (m.d 0 3) (by simp) with h15551 | h15551
                            · linarith only [h14399, h15551, hlam]
                            · rcases p15436_3 (m.d 0 4) (by simp) with h15553 | h15553
                              · linarith only [h14400, h15553, hlam]
                              · rcases p15436_3 (m.d 0 5) (by simp) with h15555 | h15555
                                · linarith only [h14401, h15555, hlam]
                                · rcases h2bigk with h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h0, hlam, p15557_1]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14396, h15420, hlam, p15436_1, p15557_2]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14397, h15421, hlam, p15436_1, p15557_2]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14398, h15422, hlam, p15436_1, p15557_2]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14397, h15420, h15423, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15436_1, p15557_1]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h0, h14397, h15420, h15423, hlam, p15436_1, p15557_2]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h0, h14397, h15421, hlam, p15436_1, p15557_2]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h0, h14398, h15422, hlam, p15436_1, p15557_2]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14399, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h15420, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h15429, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h15431, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14400, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h15421, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14398, h15421, h15427, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15436_1, p15557_1]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h15433, hlam, p15557_1]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h14401, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h15422, hlam, p15557_0]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15436_1, p15557_1]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15436_1, p15557_1]
                                  · have p15557_0 := h15557c.1
                                    have p15557_1 := h15557c.2.1
                                    have p15557_2 := h15557c.2.2.1
                                    have p15557_3 := h15557c.2.2.2
                                    linarith only [hlam, p15557_0]
                          · linarith only [h0, h15550, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15585 | h15585
                        · linarith only [h0, h15585, hlam]
                        · linarith only [h14396, h15585, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15588 | h15588
                        · linarith only [h0, h15588, hlam]
                        · linarith only [h14397, h15588, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        rcases p15436_3 (m.d 0 1) (by simp) with h15591 | h15591
                        · linarith only [h0, h15591, hlam]
                        · linarith only [h14398, h15591, hlam]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14396, hlam, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14399, hlam, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14402, hlam, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14861, hlam, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14397, hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14400, hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h15018, hc03, hc45, hlam, hphi, ht34, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h15018, hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14398, hlam, p15436_0]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14401, hlam, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14396, h15018, h15420, h15435, hc23, hc34, hlam, hphi, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [h14400, h15018, h15429, h15435, hc23, hc34, hlam, hphi, p15436_1]
                      · have p15436_0 := h15436c.1
                        have p15436_1 := h15436c.2.1
                        have p15436_2 := h15436c.2.2.1
                        have p15436_3 := h15436c.2.2.2
                        linarith only [hlam, p15436_0]
                    · rcases h0bigk with h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c | h15609c
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h0, hlam, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15612 | h15612
                        · rcases p15609_3 (m.d 0 2) (by simp) with h15613 | h15613
                          · rcases p15609_3 (m.d 0 3) (by simp) with h15614 | h15614
                            · linarith only [h14396, h15614, hlam]
                            · rcases p15609_3 (m.d 0 4) (by simp) with h15616 | h15616
                              · linarith only [h14397, h15616, hlam]
                              · linarith only [h14402, h15616, hlam]
                          · linarith only [h14399, h15613, hlam]
                        · linarith only [h14396, h15612, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15621 | h15621
                        · rcases p15609_3 (m.d 0 2) (by simp) with h15622 | h15622
                          · rcases p15609_3 (m.d 0 3) (by simp) with h15623 | h15623
                            · linarith only [h14396, h15623, hlam]
                            · rcases p15609_3 (m.d 0 4) (by simp) with h15625 | h15625
                              · linarith only [h14397, h15625, hlam]
                              · rcases p15609_3 (m.d 0 5) (by simp) with h15627 | h15627
                                · linarith only [h14398, h15627, hlam]
                                · linarith only [h15018, h15627, hlam]
                          · linarith only [h14400, h15622, hlam]
                        · linarith only [h14397, h15621, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15632 | h15632
                        · rcases p15609_3 (m.d 0 2) (by simp) with h15633 | h15633
                          · rcases p15609_3 (m.d 0 3) (by simp) with h15634 | h15634
                            · linarith only [h14396, h15634, hlam]
                            · rcases p15609_3 (m.d 0 4) (by simp) with h15636 | h15636
                              · linarith only [h14397, h15636, hlam]
                              · rcases p15609_3 (m.d 0 5) (by simp) with h15638 | h15638
                                · linarith only [h14398, h15638, hlam]
                                · rcases h2bigk with h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c | h15640c
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, hlam, p15640_1]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    rcases p15640_3 (m.d 0 2) (by simp) with h15643 | h15643
                                    · rcases p15640_3 (m.d 1 2) (by simp) with h15644 | h15644
                                      · rcases p15640_3 (m.d 2 3) (by simp) with h15645 | h15645
                                        · linarith only [h15645, hlam, p15640_0]
                                        · rcases p15640_3 (m.d 2 4) (by simp) with h15647 | h15647
                                          · linarith only [h14400, h15647, hlam]
                                          · linarith only [h15429, h15647, hlam]
                                      · linarith only [h15420, h15644, hlam]
                                    · linarith only [h15643, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    rcases p15640_3 (m.d 0 2) (by simp) with h15652 | h15652
                                    · rcases p15640_3 (m.d 1 2) (by simp) with h15653 | h15653
                                      · rcases p15640_3 (m.d 2 3) (by simp) with h15654 | h15654
                                        · linarith only [h14399, h15654, hlam]
                                        · rcases p15640_3 (m.d 2 4) (by simp) with h15656 | h15656
                                          · linarith only [h15656, hlam, p15640_0]
                                          · rcases p15640_3 (m.d 2 5) (by simp) with h15658 | h15658
                                            · linarith only [h14401, h15658, hlam]
                                            · linarith only [h15433, h15658, hlam]
                                      · linarith only [h15421, h15653, hlam]
                                    · linarith only [h15652, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    rcases p15640_3 (m.d 0 2) (by simp) with h15663 | h15663
                                    · rcases p15640_3 (m.d 1 2) (by simp) with h15664 | h15664
                                      · rcases p15640_3 (m.d 2 3) (by simp) with h15665 | h15665
                                        · linarith only [h14399, h15665, hlam]
                                        · rcases p15640_3 (m.d 2 4) (by simp) with h15667 | h15667
                                          · linarith only [h14400, h15667, hlam]
                                          · rcases p15640_3 (m.d 2 5) (by simp) with h15669 | h15669
                                            · linarith only [h15669, hlam, p15640_0]
                                            · rcases h3bigk with h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c | h15671c
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14402, h15420, hc23, hc34, hlam, hphi, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14402, h15435, hc23, hc45, hlam, hphi, ht34, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14402, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14861, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14396, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h0, h14396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15423, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15425, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14399, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15420, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15429, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15431, hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15435, hc03, hc45, hlam, hphi, ht34, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15420, h15435, hc23, hc45, hlam, hphi, ht34, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15435, hc23, hc45, hlam, hphi, ht34, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [hlam, p15671_0]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15435, hlam, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h14396, h15420, hc23, hc35, hlam, hphi, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15420, hc23, hc35, hlam, hphi, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [h15435, hc34, hc45, hlam, hphi, p15671_1]
                                              · have p15671_0 := h15671c.1
                                                have p15671_1 := h15671c.2.1
                                                have p15671_2 := h15671c.2.2.1
                                                have p15671_3 := h15671c.2.2.2
                                                linarith only [hlam, p15671_0]
                                      · linarith only [h15422, h15664, hlam]
                                    · linarith only [h15663, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p15609_1, p15640_1]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, h14396, h14402, h15018, h15420, hlam, p15609_1, p15640_2]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, h14400, h15018, hlam, p15609_1, p15640_2]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, h14398, h15422, hlam, p15609_1, p15640_2]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h14399, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h15420, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h15429, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h15431, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h14400, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h15421, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h14397, h15018, h15421, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15609_1, p15640_1]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h15433, hlam, p15640_1]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h14401, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h15422, hlam, p15640_0]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15609_1, p15640_1]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15609_1, p15640_1]
                                  · have p15640_0 := h15640c.1
                                    have p15640_1 := h15640c.2.1
                                    have p15640_2 := h15640c.2.2.1
                                    have p15640_3 := h15640c.2.2.2
                                    linarith only [hlam, p15640_0]
                          · linarith only [h14401, h15633, hlam]
                        · linarith only [h14398, h15632, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15721 | h15721
                        · linarith only [h0, h15721, hlam]
                        · rcases p15609_3 (m.d 0 2) (by simp) with h15723 | h15723
                          · rcases p15609_3 (m.d 0 3) (by simp) with h15724 | h15724
                            · linarith only [h14399, h15724, hlam]
                            · rcases p15609_3 (m.d 0 4) (by simp) with h15726 | h15726
                              · linarith only [h14400, h15726, hlam]
                              · rcases p15609_3 (m.d 0 5) (by simp) with h15728 | h15728
                                · linarith only [h14401, h15728, hlam]
                                · rcases h2bigk with h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c | h15730c
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h0, hlam, p15730_1]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14396, h15420, hlam, p15609_1, p15730_2]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14397, h15421, hlam, p15609_1, p15730_2]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14398, h15422, hlam, p15609_1, p15730_2]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14397, h15420, h15423, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15609_1, p15730_1]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h0, h14397, h15420, h15423, hlam, p15609_1, p15730_2]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h0, h14397, h15421, hlam, p15609_1, p15730_2]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h0, h14398, h15422, hlam, p15609_1, p15730_2]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14399, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h15420, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h15429, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h15431, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14400, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h15421, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14398, h15421, h15427, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15609_1, p15730_1]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h15433, hlam, p15730_1]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h14401, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h15422, hlam, p15730_0]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15609_1, p15730_1]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15609_1, p15730_1]
                                  · have p15730_0 := h15730c.1
                                    have p15730_1 := h15730c.2.1
                                    have p15730_2 := h15730c.2.2.1
                                    have p15730_3 := h15730c.2.2.2
                                    linarith only [hlam, p15730_0]
                          · linarith only [h0, h15723, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15758 | h15758
                        · linarith only [h0, h15758, hlam]
                        · linarith only [h14396, h15758, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15761 | h15761
                        · linarith only [h0, h15761, hlam]
                        · linarith only [h14397, h15761, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15764 | h15764
                        · linarith only [h0, h15764, hlam]
                        · linarith only [h14398, h15764, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14396, hlam, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14399, hlam, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14402, hlam, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14861, hlam, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14397, hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14400, hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14396, h15018, h15420, hc23, hc45, hlam, hphi, ht34, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h15018, hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14398, hlam, p15609_0]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [h14401, hlam, p15609_1]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15779 | h15779
                        · rcases p15609_3 (m.d 0 2) (by simp) with h15780 | h15780
                          · rcases p15609_3 (m.d 0 3) (by simp) with h15781 | h15781
                            · linarith only [h14861, h15781, hlam]
                            · rcases p15609_3 (m.d 0 4) (by simp) with h15783 | h15783
                              · linarith only [h15018, h15783, hlam]
                              · linarith only [h14402, h15783, hlam]
                          · linarith only [h14399, h15780, hlam]
                        · linarith only [h14396, h15779, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        rcases p15609_3 (m.d 0 1) (by simp) with h15788 | h15788
                        · rcases p15609_3 (m.d 0 2) (by simp) with h15789 | h15789
                          · rcases p15609_3 (m.d 0 3) (by simp) with h15790 | h15790
                            · linarith only [h14861, h15790, hlam]
                            · rcases p15609_3 (m.d 0 4) (by simp) with h15792 | h15792
                              · linarith only [h15018, h15792, hlam]
                              · rcases p15609_3 (m.d 0 5) (by simp) with h15794 | h15794
                                · rcases h2bigk with h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c | h15795c
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h0, hlam, p15795_1]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    rcases p15795_3 (m.d 0 2) (by simp) with h15798 | h15798
                                    · rcases p15795_3 (m.d 1 2) (by simp) with h15799 | h15799
                                      · rcases p15795_3 (m.d 2 3) (by simp) with h15800 | h15800
                                        · linarith only [h15800, hlam, p15795_0]
                                        · rcases p15795_3 (m.d 2 4) (by simp) with h15802 | h15802
                                          · linarith only [h14400, h15802, hlam]
                                          · linarith only [h15429, h15802, hlam]
                                      · linarith only [h15420, h15799, hlam]
                                    · linarith only [h15798, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    rcases p15795_3 (m.d 0 2) (by simp) with h15807 | h15807
                                    · rcases p15795_3 (m.d 1 2) (by simp) with h15808 | h15808
                                      · rcases p15795_3 (m.d 2 3) (by simp) with h15809 | h15809
                                        · linarith only [h14399, h15809, hlam]
                                        · rcases p15795_3 (m.d 2 4) (by simp) with h15811 | h15811
                                          · linarith only [h15811, hlam, p15795_0]
                                          · rcases p15795_3 (m.d 2 5) (by simp) with h15813 | h15813
                                            · linarith only [h14401, h15813, hlam]
                                            · linarith only [h15433, h15813, hlam]
                                      · linarith only [h15421, h15808, hlam]
                                    · linarith only [h15807, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    rcases p15795_3 (m.d 0 2) (by simp) with h15818 | h15818
                                    · rcases p15795_3 (m.d 1 2) (by simp) with h15819 | h15819
                                      · rcases p15795_3 (m.d 2 3) (by simp) with h15820 | h15820
                                        · linarith only [h14399, h15820, hlam]
                                        · rcases p15795_3 (m.d 2 4) (by simp) with h15822 | h15822
                                          · linarith only [h14400, h15822, hlam]
                                          · rcases p15795_3 (m.d 2 5) (by simp) with h15824 | h15824
                                            · linarith only [h15824, hlam, p15795_0]
                                            · rcases h3bigk with h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c | h15826c
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h14398, h14402, h15420, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15609_1, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h0, h14398, h14402, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15609_1, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h14402, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h14861, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h14396, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h0, h14396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15423, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15425, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h14399, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15420, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15429, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15431, hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15435, hc03, hc45, hlam, hphi, ht34, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15420, h15435, hc23, hc45, hlam, hphi, ht34, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15435, hc23, hc45, hlam, hphi, ht34, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [hlam, p15826_0]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15435, hlam, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h14396, h15420, h15435, hc23, hc45, hlam, hphi, ht34, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15420, h15435, hc23, hc45, hlam, hphi, ht34, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15435, hc23, hc45, hlam, hphi, ht34, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [h15435, hc34, hc45, hlam, hphi, p15826_1]
                                              · have p15826_0 := h15826c.1
                                                have p15826_1 := h15826c.2.1
                                                have p15826_2 := h15826c.2.2.1
                                                have p15826_3 := h15826c.2.2.2
                                                linarith only [hlam, p15826_0]
                                      · linarith only [h15422, h15819, hlam]
                                    · linarith only [h15818, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h0, h14398, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p15609_1, p15795_1]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h0, h14396, h14398, h14402, h15420, hlam, p15609_1, p15795_2]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h0, h14398, h14400, hlam, p15609_1, p15795_2]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    rcases p15795_3 (m.d 0 2) (by simp) with h15858 | h15858
                                    · linarith only [h0, h15858, hlam]
                                    · linarith only [h14401, h15858, hlam]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h14399, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h15420, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h15429, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h15431, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h14400, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h15421, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h14398, h14400, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15609_1, p15795_1]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h15433, hlam, p15795_1]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h14401, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h15422, hlam, p15795_0]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15795_1]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [h0, h14398, h15422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15795_1]
                                  · have p15795_0 := h15795c.1
                                    have p15795_1 := h15795c.2.1
                                    have p15795_2 := h15795c.2.2.1
                                    have p15795_3 := h15795c.2.2.2
                                    linarith only [hlam, p15795_0]
                                · linarith only [h15018, h15794, hlam]
                          · linarith only [h14400, h15789, hlam]
                        · linarith only [h14397, h15788, hlam]
                      · have p15609_0 := h15609c.1
                        have p15609_1 := h15609c.2.1
                        have p15609_2 := h15609c.2.2.1
                        have p15609_3 := h15609c.2.2.2
                        linarith only [hlam, p15609_0]
      · linarith only [h0, h14398, h14401, h15422, hc02, hc15, hlam, hphi, ht0b, ht5b]
    · linarith only [h0, h14400, h15421, hlam]
  · linarith only [h0, h14399, h15420, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14402 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h14861 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 4 5 (by decide) (by decide) with h15018 | h15018
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401 h14402 h14861 h15018
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401 h14402 h14861 h15018

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14402 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 3 5 (by decide) (by decide) with h14861 | h14861
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401 h14402 h14861
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401 h14402 h14861

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 3 4 (by decide) (by decide) with h14402 | h14402
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401 h14402
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401 h14402

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0 := hg0
  have h14396 := hg14396
  linarith only [h0, h14398, h14401, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 2 5 (by decide) (by decide) with h14401 | h14401
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400 h14401

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h14396 := hg14396
  linarith only [h0, h14397, h14400, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 2 4 (by decide) (by decide) with h14400 | h14400
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399 h14400

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0 := hg0
  have h14396 := hg14396
  linarith only [h0, h14396, h14399, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 2 3 (by decide) (by decide) with h14399 | h14399
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398 h14399

end R2N4
