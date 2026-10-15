import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S0
import Jsp000404.R1LeavesN7_46S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h2493 | h2493
  · linarith only [h2493, h559, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2495 | h2495
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2496 | h2496
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2497 | h2497
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2498 | h2498
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2499 | h2499
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2500 | h2500
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2501 | h2501
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2502 | h2502
                  · linarith only [h2502, h556, h559, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2504 | h2504
                    · linarith only [h2493, h2504, h556, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2506 | h2506
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2507 | h2507
                        · rcases h0bigk with h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h0, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h451, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h0, h2493, h2495, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2508_1, u2ehi2]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2493, h451, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2514 | h2514
                            · linarith only [h0, h2514, hlam]
                            · rcases p2508_3 (m.d 0 2) (by simp) with h2516 | h2516
                              · rcases p2508_3 (m.d 0 3) (by simp) with h2517 | h2517
                                · linarith only [h2517, h556, hlam]
                                · linarith only [h2517, h451, hlam]
                              · linarith only [h0, h2516, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2522 | h2522
                            · linarith only [h0, h2522, hlam]
                            · rcases p2508_3 (m.d 0 2) (by simp) with h2524 | h2524
                              · rcases p2508_3 (m.d 0 3) (by simp) with h2525 | h2525
                                · linarith only [h2525, h556, hlam]
                                · rcases p2508_3 (m.d 0 4) (by simp) with h2527 | h2527
                                  · linarith only [h2527, h557, hlam]
                                  · linarith only [h2527, h559, hlam]
                              · linarith only [h2524, h556, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2531 | h2531
                            · linarith only [h0, h2531, hlam]
                            · rcases p2508_3 (m.d 0 2) (by simp) with h2533 | h2533
                              · rcases p2508_3 (m.d 0 3) (by simp) with h2534 | h2534
                                · linarith only [h2534, h556, hlam]
                                · rcases p2508_3 (m.d 0 4) (by simp) with h2536 | h2536
                                  · linarith only [h2536, h557, hlam]
                                  · rcases p2508_3 (m.d 0 5) (by simp) with h2538 | h2538
                                    · linarith only [h2538, h558, hlam]
                                    · rcases h0emin with h2540 | h2540 | h2540 | h2540 | h2540
                                      · linarith only [h0, h2540, hc12, hlam, ht01]
                                      · rcases h3bigk with h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h451, hlam, p2542_1]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2493, h2495, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2508_1, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h559, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2493, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          rcases p2542_3 (m.d 0 3) (by simp) with h2548 | h2548
                                          · linarith only [h2548, h451, hlam]
                                          · rcases p2542_3 (m.d 1 3) (by simp) with h2550 | h2550
                                            · rcases p2542_3 (m.d 2 3) (by simp) with h2551 | h2551
                                              · linarith only [h2496, h2551, hlam]
                                              · rcases p2542_3 (m.d 3 4) (by simp) with h2553 | h2553
                                                · linarith only [h2499, h2553, hlam]
                                                · linarith only [h2553, h559, hlam]
                                            · linarith only [h2550, h451, hlam]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          rcases p2542_3 (m.d 0 3) (by simp) with h2558 | h2558
                                          · linarith only [h2558, h451, hlam]
                                          · linarith only [h2558, h556, hlam]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2493, h2507, h451, hc01, hc13, hlam, hphi, p2542_1]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2493, h2496, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h556, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2496, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2502, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2504, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h556, hc34, hlam, hphi, ht23, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2499, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2496, h2499, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2493, h2496, h2499, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h556, hc35, hlam, hphi, ht23, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2500, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2496, h2500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2542_1, u2ehi2]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [h2507, hlam, p2542_0]
                                        · have p2542_0 := h2542c.1
                                          have p2542_1 := h2542c.2.1
                                          have p2542_2 := h2542c.2.2.1
                                          have p2542_3 := h2542c.2.2.2
                                          linarith only [hlam, p2542_0]
                                      · linarith only [h2496, h2499, h2540, h559, hc12, hlam, ht01]
                                      · linarith only [h0, h2540, hc12, hlam, ht01, p2508_1]
                                      · linarith only [h0, h2495, h2540, hc12, hlam, ht01, p2508_1]
                              · linarith only [h2533, h557, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2582 | h2582
                            · linarith only [h0, h2582, hlam]
                            · rcases p2508_3 (m.d 0 2) (by simp) with h2584 | h2584
                              · rcases p2508_3 (m.d 0 3) (by simp) with h2585 | h2585
                                · linarith only [h2585, h556, hlam]
                                · rcases p2508_3 (m.d 0 4) (by simp) with h2587 | h2587
                                  · linarith only [h2587, h557, hlam]
                                  · linarith only [h2495, h2587, hlam]
                              · linarith only [h2584, h558, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2496, h2499, h559, hc01, hc12, hlam, hphi, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h556, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h559, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2493, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2496, h2499, h559, hc01, hc12, hlam, hphi, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h557, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2496, h2499, h559, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2508_1, u3ehi0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2493, h2496, h2499, h556, h559, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2508_1, u2ehi2]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2493, h2496, h2499, h2507, hc01, hc12, hlam, hphi, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h558, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2493, h2496, h2499, h2507, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2508_1, u2ehi2]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2495, hlam, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                        · linarith only [h0, h2506, h2507, h557, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2495, h2496, h2499, h2506, h559, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h2495, h2496, h2497, h2499, h2501, h559, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h2499, h2500, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2610 | h2610
              · linarith only [h2499, h2610, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2612 | h2612
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2613 | h2613
                  · linarith only [h2499, h2613, h451, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2615 | h2615
                    · linarith only [h2610, h2613, h2615, h451, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2617 | h2617
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2618 | h2618
                        · rcases h0bigk with h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [hlam, p2619_0]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h0, hlam, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h451, hlam, p2619_0]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h0, h2493, h2495, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi2]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h2493, h451, h556, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi2]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            rcases p2619_3 (m.d 0 1) (by simp) with h2625 | h2625
                            · linarith only [h0, h2625, hlam]
                            · rcases p2619_3 (m.d 0 2) (by simp) with h2627 | h2627
                              · rcases p2619_3 (m.d 0 3) (by simp) with h2628 | h2628
                                · linarith only [h2628, h556, hlam]
                                · linarith only [h2628, h451, hlam]
                              · linarith only [h0, h2627, hlam]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [hlam, p2619_0]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            rcases p2619_3 (m.d 0 1) (by simp) with h2633 | h2633
                            · linarith only [h0, h2633, hlam]
                            · rcases p2619_3 (m.d 0 2) (by simp) with h2635 | h2635
                              · rcases p2619_3 (m.d 0 3) (by simp) with h2636 | h2636
                                · linarith only [h2636, h556, hlam]
                                · rcases p2619_3 (m.d 0 4) (by simp) with h2638 | h2638
                                  · linarith only [h2638, h557, hlam]
                                  · linarith only [h2638, h559, hlam]
                              · linarith only [h2635, h556, hlam]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            rcases p2619_3 (m.d 0 1) (by simp) with h2642 | h2642
                            · linarith only [h0, h2642, hlam]
                            · rcases p2619_3 (m.d 0 2) (by simp) with h2644 | h2644
                              · rcases p2619_3 (m.d 0 3) (by simp) with h2645 | h2645
                                · linarith only [h2645, h556, hlam]
                                · rcases p2619_3 (m.d 0 4) (by simp) with h2647 | h2647
                                  · linarith only [h2647, h557, hlam]
                                  · rcases p2619_3 (m.d 0 5) (by simp) with h2649 | h2649
                                    · linarith only [h2649, h558, hlam]
                                    · rcases h0emin with h2651 | h2651 | h2651 | h2651 | h2651
                                      · linarith only [h2610, h2618, h2651, h451, hc34, hlam, ht01, ht12, ht23]
                                      · rcases h3bigk with h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c | h2653c
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h451, hlam, p2653_1]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h0, h2493, h2495, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h559, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2493, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2610, h2618, hc34, hlam, hphi, p2653_1, u3ehi0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2610, h2618, hc34, hlam, hphi, ht23, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2499, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2610, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h556, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2496, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2613, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2615, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h556, hc34, hlam, hphi, ht23, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h451, hc01, hc34, hlam, hphi, ht12, ht23, p2653_1]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hc34, hlam, hphi, ht23, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hc34, hlam, hphi, p2653_1, u3ehi4]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h556, hc35, hlam, hphi, ht23, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h0, h2495, h2615, h451, h558, hc01, hc12, hc35, hlam, hphi, ht23, p2619_1, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht23, p2653_1, u2ehi2]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [h2618, hlam, p2653_0]
                                        · have p2653_0 := h2653c.1
                                          have p2653_1 := h2653c.2.1
                                          have p2653_2 := h2653c.2.2.1
                                          have p2653_3 := h2653c.2.2.2
                                          linarith only [hlam, p2653_0]
                                      · linarith only [h0, h2495, h2615, h2651, h558, h559, hc12, hc34, hlam, hphi, ht01, ht23, p2619_1, u2ehi2]
                                      · linarith only [h0, h2651, hc12, hlam, ht01, p2619_1]
                                      · linarith only [h0, h2495, h2651, hc12, hlam, ht01, p2619_1]
                              · linarith only [h2644, h557, hlam]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            rcases p2619_3 (m.d 0 1) (by simp) with h2683 | h2683
                            · linarith only [h0, h2683, hlam]
                            · rcases p2619_3 (m.d 0 2) (by simp) with h2685 | h2685
                              · rcases p2619_3 (m.d 0 3) (by simp) with h2686 | h2686
                                · linarith only [h2686, h556, hlam]
                                · rcases p2619_3 (m.d 0 4) (by simp) with h2688 | h2688
                                  · linarith only [h2688, h557, hlam]
                                  · linarith only [h2495, h2688, hlam]
                              · linarith only [h2685, h558, hlam]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h559, hc01, hc34, hlam, hphi, ht12, ht23, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h556, hlam, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [hlam, p2619_0]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h559, hlam, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h2493, hlam, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            rcases p2619_3 (m.d 0 1) (by simp) with h2697 | h2697
                            · linarith only [h2697, hlam, p2619_0]
                            · rcases p2619_3 (m.d 0 2) (by simp) with h2699 | h2699
                              · rcases p2619_3 (m.d 0 3) (by simp) with h2700 | h2700
                                · linarith only [h2700, h559, hlam]
                                · linarith only [h2700, h451, hlam]
                              · linarith only [h0, h2699, hlam]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h557, hlam, p2619_0]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h556, h559, hc34, hlam, hphi, ht23, p2619_1, u2ehi2]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [hlam, p2619_0]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h2493, h556, h559, hc34, hlam, hphi, ht23, p2619_1, u2ehi2]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            rcases p2619_3 (m.d 0 1) (by simp) with h2708 | h2708
                            · linarith only [h2708, hlam, p2619_0]
                            · rcases p2619_3 (m.d 0 2) (by simp) with h2710 | h2710
                              · rcases p2619_3 (m.d 0 3) (by simp) with h2711 | h2711
                                · linarith only [h2493, h2711, hlam]
                                · linarith only [h2711, h451, hlam]
                              · linarith only [h0, h2710, hlam]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h558, hlam, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h2493, h2618, h556, hc34, hlam, hphi, ht23, p2619_1, u2ehi2]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [h2495, hlam, p2619_1]
                          · have p2619_0 := h2619c.1
                            have p2619_1 := h2619c.2.1
                            have p2619_2 := h2619c.2.2.1
                            have p2619_3 := h2619c.2.2.2
                            linarith only [hlam, p2619_0]
                        · linarith only [h0, h2617, h2618, h557, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2495, h2613, h2617, h559, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h2495, h2497, h2612, h559, hc34, hlam, hphi, ht23, u2ehi3]
          · linarith only [h0, h2498, h556, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h2497, h556, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h2496, h556, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2725 | h2725
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2726 | h2726
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2727 | h2727
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2728 | h2728
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2729 | h2729
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2730 | h2730
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2731 | h2731
                  · linarith only [h2731, h556, h559, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2733 | h2733
                    · linarith only [h2495, h2725, h2728, h2730, h2733, h556, h559, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2735 | h2735
                      · linarith only [h2495, h2735, h556, h557, h559, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2737 | h2737
                        · linarith only [h2495, h2737, h556, h559, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h2730, h2737, h556, h559, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h2728, h2730, h556, h559, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h2728, h2729, h556, h559, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2742 | h2742
              · linarith only [h2728, h2742, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2744 | h2744
                · linarith only [h2495, h2728, h2744, h556, h559, hc34, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2746 | h2746
                  · linarith only [h2728, h2744, h2746, h451, h556, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2748 | h2748
                    · linarith only [h2742, h2748, h451, h556, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2750 | h2750
                      · linarith only [h2728, h2744, h2750, h451, h556, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2752 | h2752
                        · linarith only [h2728, h2744, h2752, h451, h556, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h2752, h556, h559, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h2727, h556, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h2726, h557, hlam]
      · linarith only [h0, h2725, h556, hlam]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h556, h558, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h558 | h558
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h556, h557, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h557 | h557
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h2760 | h2760
  · linarith only [h2760, h556, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2762 | h2762
    · linarith only [h2762, h556, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2764 | h2764
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2765 | h2765
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2766 | h2766
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2767 | h2767
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2768 | h2768
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2769 | h2769
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2770 | h2770
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2771 | h2771
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2772 | h2772
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2773 | h2773
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2774 | h2774
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2775 | h2775
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2776 | h2776
                              · rcases h0bigk with h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h0, hlam, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h451, hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h0, h2762, h2766, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h0, h2762, hlam, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2762, h2769, h2770, h2772, hc01, hc13, hlam, hphi, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h556, hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2760, hlam, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2762, hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2767, h556, hc01, hc12, hlam, hphi, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2767, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2762, h2766, h2767, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2762, h2767, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2764, h2767, h556, hc01, hc12, hlam, hphi, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2760, hc24, hlam, hphi, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2764, hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2762, h2764, h2767, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2765, h2767, h556, hc01, hc12, hlam, hphi, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2762, hc25, hlam, hphi, p2777_1, u2ehi0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2765, hlam, p2777_0]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [h2766, hlam, p2777_1]
                                · have p2777_0 := h2777c.1
                                  have p2777_1 := h2777c.2.1
                                  have p2777_2 := h2777c.2.2.1
                                  have p2777_3 := h2777c.2.2.2
                                  linarith only [hlam, p2777_0]
                              · linarith only [h2764, h2766, h2767, h2776, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h2764, h2766, h2767, h2775, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h2774, h556, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h2773, h556, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2760, h2764, h2766, h2768, h2772, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h2765, h2767, h2771, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h2764, h2767, h2770, h556, hlam]
                · linarith only [h2767, h2769, hc25, hlam, hphi, u2ehi2]
              · linarith only [h2767, h2768, h556, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2812 | h2812
              · linarith only [h2767, h2812, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2814 | h2814
                · linarith only [h2767, h2814, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2816 | h2816
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2817 | h2817
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2818 | h2818
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2819 | h2819
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2820 | h2820
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2821 | h2821
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2822 | h2822
                              · rcases h0bigk with h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c | h2823c
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h0, hlam, p2823_1]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h451, hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h0, h2762, h2766, h2814, h2819, h2821, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h0, h2762, h2814, h2819, h2821, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h0, h2814, h2819, h2821, hc01, hc23, hlam, hphi, ht12, p2823_1]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h556, hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2760, hlam, p2823_1]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2762, hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  rcases p2823_3 (m.d 0 1) (by simp) with h2834 | h2834
                                  · linarith only [h2834, h451, hlam]
                                  · rcases p2823_3 (m.d 0 2) (by simp) with h2836 | h2836
                                    · linarith only [h2836, h556, hlam]
                                    · linarith only [h0, h2836, hlam]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2767, h451, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2762, h2766, h2767, h451, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2762, h2767, h451, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  rcases p2823_3 (m.d 0 1) (by simp) with h2843 | h2843
                                  · linarith only [h2843, hlam, p2823_0]
                                  · rcases p2823_3 (m.d 0 2) (by simp) with h2845 | h2845
                                    · linarith only [h2760, h2845, hlam]
                                    · linarith only [h0, h2845, hlam]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2760, h2819, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2764, hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2762, h2764, h2767, h451, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  rcases p2823_3 (m.d 0 1) (by simp) with h2852 | h2852
                                  · linarith only [h2852, hlam, p2823_0]
                                  · rcases p2823_3 (m.d 0 2) (by simp) with h2854 | h2854
                                    · linarith only [h2762, h2854, hlam]
                                    · linarith only [h0, h2854, hlam]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2762, h2819, h2821, hc23, hlam, hphi, p2823_1, u2ehi0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2765, hlam, p2823_0]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [h2766, hlam, p2823_1]
                                · have p2823_0 := h2823c.1
                                  have p2823_1 := h2823c.2.1
                                  have p2823_2 := h2823c.2.2.1
                                  have p2823_3 := h2823c.2.2.2
                                  linarith only [hlam, p2823_0]
                              · rcases h0bigk with h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h451, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, h2814, h2819, h2821, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, h2814, h2819, h2821, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, h2814, h2819, h2821, hc01, hc23, hlam, hphi, ht12, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h556, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2760, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2762, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  rcases p2861_3 (m.d 0 1) (by simp) with h2872 | h2872
                                  · linarith only [h2872, h451, hlam]
                                  · rcases p2861_3 (m.d 0 2) (by simp) with h2874 | h2874
                                    · linarith only [h2874, h556, hlam]
                                    · linarith only [h0, h2874, hlam]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2767, h451, hc23, hlam, hphi, p2861_1, u2ehi0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2766, h2767, h2822, h451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2861_1, u3ehi3]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2762, h2767, h451, hc23, hlam, hphi, p2861_1, u2ehi0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  rcases p2861_3 (m.d 0 1) (by simp) with h2881 | h2881
                                  · linarith only [h2881, hlam, p2861_0]
                                  · rcases p2861_3 (m.d 0 2) (by simp) with h2883 | h2883
                                    · linarith only [h2760, h2883, hlam]
                                    · linarith only [h0, h2883, hlam]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2760, h2819, hc23, hlam, hphi, p2861_1, u2ehi0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2764, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2764, h2766, h2767, h2822, h451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2861_1, u3ehi3]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  rcases p2861_3 (m.d 0 1) (by simp) with h2890 | h2890
                                  · linarith only [h2890, hlam, p2861_0]
                                  · rcases p2861_3 (m.d 0 2) (by simp) with h2892 | h2892
                                    · linarith only [h2762, h2892, hlam]
                                    · linarith only [h0, h2892, hlam]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2762, h2819, h2821, hc23, hlam, hphi, p2861_1, u2ehi0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2765, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2766, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                            · linarith only [h2760, h2818, h2821, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h2820, h556, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h2764, h2767, h2819, h451, hlam]
                      · linarith only [h0, h2764, h2766, h2812, h2818, h451, hc01, hc13, hlam, hphi]
                    · linarith only [h2765, h2817, h451, hlam]
                  · linarith only [h2764, h2816, h451, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2905 | h2905
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2906 | h2906
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2907 | h2907
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2908 | h2908
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2909 | h2909
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2910 | h2910
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2911 | h2911
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2912 | h2912
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2913 | h2913
                            · linarith only [h2760, h2766, h2913, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h2760, h2905, h2908, h2910, h2913, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h2765, h2912, h556, hlam]
                        · linarith only [h2764, h2766, h2905, h2908, h2910, h2911, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h2760, h2906, h2910, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h2765, h2909, h451, h556, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h2765, h2905, h2908, h556, hc34, hlam, hphi, u3ehi4]
                · linarith only [h2905, h2907, hc25, hlam, hphi, u2ehi2]
              · linarith only [h2905, h2906, h556, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2923 | h2923
              · linarith only [h2905, h2923, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2925 | h2925
                · linarith only [h2905, h2925, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2927 | h2927
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2928 | h2928
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2929 | h2929
                      · linarith only [h2760, h2766, h2923, h2929, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2931 | h2931
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2932 | h2932
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2933 | h2933
                            · linarith only [h2923, h2929, h2931, h2933, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h2760, h2933, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h2765, h2905, h2932, h451, hlam]
                        · linarith only [h2765, h2905, h2931, h451, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h2765, h2928, h451, hlam]
                  · linarith only [h2764, h2927, h451, hlam]
        · linarith only [h2764, h2765, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2941 | h2941
        · linarith only [h2764, h2941, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2943 | h2943
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2944 | h2944
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2945 | h2945
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2946 | h2946
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2947 | h2947
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2948 | h2948
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2949 | h2949
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2950 | h2950
                        · linarith only [h2764, h2944, h2950, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h2950, h556, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2760, h2943, h2945, h2949, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h2947, h2948, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2944, h2947, h556, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2944, h2946, h556, hc25, hlam, hphi, u2ehi0]
              · linarith only [h2944, h2945, h556, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2958 | h2958
              · linarith only [h2944, h2958, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2960 | h2960
                · linarith only [h2944, h2960, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2962 | h2962
                  · linarith only [h2764, h2944, h2962, h556, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2964 | h2964
                    · linarith only [h2962, h2964, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2966 | h2966
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2967 | h2967
                        · linarith only [h0, h2944, h2962, h2967, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h2967, h556, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h2764, h2943, h2958, h2966, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2971 | h2971
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2972 | h2972
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2973 | h2973
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2974 | h2974
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2975 | h2975
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2976 | h2976
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2977 | h2977
                        · linarith only [h2764, h2977, h556, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2977, h556, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2760, h2972, h2976, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h2974, h2975, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2971, h2974, h556, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2971, h2973, h556, hc25, hlam, hphi, u2ehi0]
              · linarith only [h2971, h2972, h556, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2985 | h2985
              · linarith only [h2971, h2985, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2987 | h2987
                · linarith only [h2971, h2987, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2989 | h2989
                  · linarith only [h2764, h2971, h2989, h556, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2991 | h2991
                    · linarith only [h2989, h2991, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2993 | h2993
                      · linarith only [h2760, h2943, h2985, h2993, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2995 | h2995
                        · linarith only [h2764, h2995, h556, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2995, h556, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h556 | h556
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0 m hb0 hb2 hb3 hg0 h451 h556
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x1 m hb0 hb2 hb3 hg0 h451 h556

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h451 | h451
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x0 m hb0 hb2 hb3 hg0 h451
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1 m hb0 hb2 hb3 hg0 h451

end R2N4
