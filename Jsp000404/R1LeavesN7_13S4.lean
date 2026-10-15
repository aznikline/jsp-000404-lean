import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h2497 | h2497
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2498 | h2498
    · linarith only [h2498, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2500 | h2500
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2501 | h2501
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2502 | h2502
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2503 | h2503
            · linarith only [h0, h2497, h2503, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2505 | h2505
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2506 | h2506
                · linarith only [h1, h2498, h2500, h2506, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2508 | h2508
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2509 | h2509
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2510 | h2510
                      · linarith only [h0, h1, h2498, h2502, h2508, h2510, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2512 | h2512
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2513 | h2513
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2514 | h2514
                            · rcases h2bigk with h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, h5, hc12, hc34, hlam, hphi, ht23, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, h2512, h2514, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h5, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, h2512, h2514, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h0, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2512, h2514, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2503, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h0, h2510, h2512, h2514, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h4, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2502, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, h2502, h2512, h2514, hc01, hc45, hlam, hphi, ht0b, ht5b, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, hc02, hc34, hlam, hphi, ht23, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, hc12, hc34, hlam, hphi, ht23, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2510, hc23, hc34, hlam, hphi, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                rcases p2515_3 (m.d 0 2) (by simp) with h2535 | h2535
                                · linarith only [h2535, h5, hlam]
                                · linarith only [h2497, h2535, hlam]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2497, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2505, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2512, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2513, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                            · linarith only [h0, h2502, h2510, h2512, h2514, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h2502, h2508, h2509, h2513, h5, hlam]
                        · linarith only [h2500, h2510, h2512, h4, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h2498, h2500, h2501, h2502, h2503, h2509, hc23, hc34, hlam, hphi]
                  · linarith only [h2498, h2500, h2508, hc13, hc34, hlam, hphi]
              · linarith only [h2497, h2502, h2505, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2502, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h2500, h2501, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2551 | h2551
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2552 | h2552
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2553 | h2553
            · linarith only [h0, h2553, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2555 | h2555
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2556 | h2556
                · linarith only [h1, h2498, h2556, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2558 | h2558
                  · linarith only [h1, h2500, h2558, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2560 | h2560
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2561 | h2561
                      · linarith only [h2497, h2498, h2552, h2558, h2561, h3, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2563 | h2563
                        · linarith only [h0, h1, h2500, h2552, h2563, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2565 | h2565
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2566 | h2566
                            · rcases h2bigk with h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, h5, hc12, hc34, hlam, hphi, ht23, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, h5, hc23, hc34, hlam, hphi, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h5, hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, h2565, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h0, hlam, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2553, hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h0, h2561, h2565, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h4, hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2552, hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, hlam, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2563, hlam, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, hc02, hc34, hlam, hphi, ht23, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2552, h2561, hc23, hc34, hlam, hphi, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, hc23, hc34, hlam, hphi, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2561, h2563, hc23, hc34, hlam, hphi, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2497, hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2555, hlam, p2567_0]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h0, h2555, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [h2565, hlam, p2567_1]
                              · have p2567_0 := h2567c.1
                                have p2567_1 := h2567c.2.1
                                have p2567_2 := h2567c.2.2.1
                                have p2567_3 := h2567c.2.2.2
                                linarith only [hlam, p2567_0]
                            · linarith only [h2561, h2566, h4, h5, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h2497, h2560, h2565, h3, h5, hlam]
                    · linarith only [h2498, h2551, h2552, h2553, h2560, hc23, hc34, hlam, hphi]
              · linarith only [h2497, h2552, h2555, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2552, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h2497, h2551, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2599 | h2599
    · linarith only [h2599, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2601 | h2601
      · linarith only [h2497, h2601, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2603 | h2603
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2604 | h2604
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2605 | h2605
            · linarith only [h0, h2605, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2607 | h2607
              · linarith only [h0, h2497, h2607, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2609 | h2609
                · linarith only [h1, h2599, h2609, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2611 | h2611
                  · linarith only [h1, h2497, h2601, h2611, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2613 | h2613
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2614 | h2614
                      · linarith only [h0, h1, h2599, h2604, h2614, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2616 | h2616
                        · linarith only [h2497, h2601, h2616, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2618 | h2618
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2619 | h2619
                            · rcases h2bigk with h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c | h2620c
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2604, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2497, h2616, hc23, hc35, hlam, hphi, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h5, hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2497, hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h0, hlam, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2605, hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2607, hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h4, hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2604, hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2614, hlam, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2616, hlam, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2614, hc02, hc34, hlam, hphi, ht23, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2604, h2614, hc23, hc34, hlam, hphi, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2614, hc23, hc34, hlam, hphi, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [hlam, p2620_0]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h0, h2497, h2604, h2614, hc23, hc34, hlam, hphi, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h0, h2604, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2604, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2616, hc23, hc35, hlam, hphi, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [h2618, hlam, p2620_1]
                              · have p2620_0 := h2620c.1
                                have p2620_1 := h2620c.2.1
                                have p2620_2 := h2620c.2.2.1
                                have p2620_3 := h2620c.2.2.2
                                linarith only [hlam, p2620_0]
                            · linarith only [h0, h2604, h2614, h2619, h5, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h2, h2604, h2613, h2618, h5, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2599, h2603, h2604, h2605, h2613, hc23, hc34, hlam, hphi]
          · linarith only [h2604, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2650 | h2650
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2651 | h2651
            · linarith only [h0, h2651, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2653 | h2653
              · linarith only [h0, h2497, h2653, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2655 | h2655
                · linarith only [h1, h2599, h2655, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2657 | h2657
                  · linarith only [h1, h2601, h2657, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2659 | h2659
                    · linarith only [h0, h2, h2603, h2650, h2659, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2661 | h2661
                      · linarith only [h0, h1, h2599, h2650, h2661, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2663 | h2663
                        · linarith only [h2601, h2603, h2663, h4, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2665 | h2665
                          · linarith only [h0, h2603, h2650, h2661, h2665, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h2650, h2665, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2650, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5

set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_22_13_15_H_I_L_I_L_I_s4 m hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2669 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h2670 | h2670
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2671 | h2671
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2672 | h2672
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2673 | h2673
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2674 | h2674
          · linarith only [h0, h2669, h2674, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2676 | h2676
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2677 | h2677
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2678 | h2678
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2679 | h2679
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2680 | h2680
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2681 | h2681
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2682 | h2682
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2683 | h2683
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2684 | h2684
                            · rcases h2bigk with h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c | h2685c
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2676, h2681, h2684, hc02, hc45, hlam, hphi, ht0b, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h4, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2681, h2684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h0, hlam, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2674, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2681, h2684, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h0, h2682, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2681, h2684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                rcases p2685_3 (m.d 0 2) (by simp) with h2700 | h2700
                                · linarith only [h2700, h4, hlam]
                                · linarith only [h2670, h2700, hlam]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2669, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2676, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2681, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h0, h2676, h2682, h2684, hc02, hc45, hlam, hphi, ht0b, ht5b, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2670, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2677, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2682, hlam, p2685_0]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [h2683, hlam, p2685_1]
                              · have p2685_0 := h2685c.1
                                have p2685_1 := h2685c.2.1
                                have p2685_2 := h2685c.2.2.1
                                have p2685_3 := h2685c.2.2.2
                                linarith only [hlam, p2685_0]
                            · linarith only [h0, h2676, h2683, h2684, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2714 | h2714
                            · linarith only [h2681, h2683, h2714, hlam]
                            · rcases h2bigk with h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h4, hc12, hc23, hlam, hphi, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h4, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h0, hlam, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2674, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h0, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                rcases p2716_3 (m.d 0 2) (by simp) with h2730 | h2730
                                · linarith only [h2730, h4, hlam]
                                · linarith only [h2669, h2730, hlam]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                rcases p2716_3 (m.d 0 2) (by simp) with h2733 | h2733
                                · linarith only [h2733, h4, hlam]
                                · linarith only [h2670, h2733, hlam]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2669, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2676, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2681, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2683, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2670, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2677, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2682, hlam, p2716_0]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [h2670, h2681, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2716_1]
                              · have p2716_0 := h2716c.1
                                have p2716_1 := h2716c.2.1
                                have p2716_2 := h2716c.2.2.1
                                have p2716_3 := h2716c.2.2.2
                                linarith only [hlam, p2716_0]
                        · linarith only [h2672, h2682, h4, hlam]
                      · linarith only [h2671, h2681, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2748 | h2748
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2749 | h2749
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2750 | h2750
                          · linarith only [h2669, h2680, h2750, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2752 | h2752
                            · linarith only [h2676, h2680, h2748, h2752, hlam]
                            · rcases h2bigk with h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c | h2754c
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h4, hc12, hc23, hlam, hphi, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h4, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2748, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h0, hlam, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2674, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h0, h2748, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h0, h2749, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                rcases p2754_3 (m.d 0 2) (by simp) with h2768 | h2768
                                · linarith only [h2768, h4, hlam]
                                · linarith only [h2669, h2768, hlam]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                rcases p2754_3 (m.d 0 2) (by simp) with h2771 | h2771
                                · linarith only [h2771, h4, hlam]
                                · linarith only [h2670, h2771, hlam]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2669, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2676, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2748, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2750, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2670, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2677, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2749, hlam, p2754_0]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [h2670, h2748, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2754_1]
                              · have p2754_0 := h2754c.1
                                have p2754_1 := h2754c.2.1
                                have p2754_2 := h2754c.2.2.1
                                have p2754_3 := h2754c.2.2.2
                                linarith only [hlam, p2754_0]
                        · linarith only [h2669, h2673, h2676, h2680, h2748, h2749, h4, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h2669, h2673, h2680, h2748, h4, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h2674, h2677, h2679, hlam]
                · linarith only [h2674, h2676, h2678, hlam]
              · linarith only [h2670, h2677, h4, hc12, hc23, hlam, hphi]
            · linarith only [h2669, h2676, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2790 | h2790
          · linarith only [h0, h2669, h2790, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2792 | h2792
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2793 | h2793
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2794 | h2794
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2795 | h2795
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2796 | h2796
                    · linarith only [h2, h2673, h2796, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2798 | h2798
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2799 | h2799
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2800 | h2800
                          · linarith only [h2, h2673, h2792, h2800, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2802 | h2802
                            · linarith only [h2, h2673, h2792, h2798, h2802, hlam]
                            · rcases h2bigk with h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c | h2804c
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h4, hc12, hc23, hlam, hphi, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h4, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2798, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2798, h2800, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h0, hlam, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2790, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h0, h2798, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h0, h2798, h2800, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                rcases p2804_3 (m.d 0 2) (by simp) with h2818 | h2818
                                · linarith only [h2818, h4, hlam]
                                · linarith only [h2669, h2818, hlam]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                rcases p2804_3 (m.d 0 2) (by simp) with h2821 | h2821
                                · linarith only [h2821, h4, hlam]
                                · linarith only [h2670, h2821, hlam]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2669, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2792, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2798, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2800, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2670, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2793, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h2799, hlam, p2804_0]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [h0, h2793, h2798, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2804_1]
                              · have p2804_0 := h2804c.1
                                have p2804_1 := h2804c.2.1
                                have p2804_2 := h2804c.2.2.1
                                have p2804_3 := h2804c.2.2.2
                                linarith only [hlam, p2804_0]
                        · linarith only [h2672, h2799, h4, hlam]
                      · linarith only [h2671, h2798, h4, hlam]
                  · linarith only [h2790, h2793, h2795, hlam]
                · linarith only [h2671, h2673, h2790, h2792, h2794, hc24, hc45, hlam, hphi]
              · linarith only [h2670, h2792, h2793, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2669, h2792, h4, hc12, hc23, hlam, hphi]
      · linarith only [h2670, h2672, h4, hlam]
    · linarith only [h2669, h2671, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2842 | h2842
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2843 | h2843
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2844 | h2844
        · linarith only [h2669, h2670, h2844, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2846 | h2846
          · linarith only [h0, h2846, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2848 | h2848
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2849 | h2849
              · linarith only [h0, h2670, h2849, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2851 | h2851
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2852 | h2852
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2853 | h2853
                    · linarith only [h2, h2844, h2853, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2855 | h2855
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2856 | h2856
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2857 | h2857
                          · linarith only [h2, h2669, h2670, h2844, h2856, h2857, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2859 | h2859
                            · linarith only [h2669, h2670, h2855, h2857, h2859, hlam]
                            · rcases h2bigk with h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2848, h2855, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h4, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2670, h2855, h2857, hc34, hc45, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2670, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2846, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, h2855, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2849, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                rcases p2861_3 (m.d 0 2) (by simp) with h2875 | h2875
                                · linarith only [h2875, h4, hlam]
                                · linarith only [h2669, h2875, hlam]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2670, h2848, h2849, h2855, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2669, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2848, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2855, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2857, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, h2848, h2855, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2848, h2855, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2856, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2855, h2857, hc34, hc45, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                        · linarith only [h2843, h2856, h4, hlam]
                      · linarith only [h0, h2842, h2848, h2855, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2891 | h2891
                    · linarith only [h2, h2844, h2891, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2893 | h2893
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2894 | h2894
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2895 | h2895
                          · linarith only [h0, h2843, h2844, h2848, h2852, h2895, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2897 | h2897
                            · linarith only [h0, h2670, h2848, h2893, h2895, h2897, hlam]
                            · rcases h2bigk with h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c | h2899c
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2848, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h4, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2893, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2670, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h0, hlam, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2846, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2843, h2846, h2852, h2893, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2849, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                rcases p2899_3 (m.d 0 2) (by simp) with h2913 | h2913
                                · linarith only [h2913, h4, hlam]
                                · linarith only [h2669, h2913, hlam]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2670, h2843, h2852, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2669, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2848, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2893, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2895, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h0, h2848, h2893, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2848, h2893, h2895, hc34, hc45, hlam, hphi, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2894, hlam, p2899_0]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [h2893, h2895, hc34, hc45, hlam, hphi, p2899_1]
                              · have p2899_0 := h2899c.1
                                have p2899_1 := h2899c.2.1
                                have p2899_2 := h2899c.2.2.1
                                have p2899_3 := h2899c.2.2.2
                                linarith only [hlam, p2899_0]
                        · linarith only [h2843, h2894, h4, hlam]
                      · linarith only [h2843, h2846, h2848, h2852, h2893, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h2842, h2844, h2846, h2848, h2851, hc24, hc45, hlam, hphi]
            · linarith only [h2669, h2848, h4, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2931 | h2931
        · linarith only [h2669, h2670, h2931, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2933 | h2933
          · linarith only [h0, h2669, h2933, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2935 | h2935
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2936 | h2936
              · linarith only [h0, h2670, h2936, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2938 | h2938
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2939 | h2939
                  · linarith only [h1, h2843, h2939, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2941 | h2941
                    · linarith only [h2, h2931, h2941, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2943 | h2943
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2944 | h2944
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2945 | h2945
                          · linarith only [h0, h2, h2843, h2931, h2935, h2944, h2945, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2947 | h2947
                            · linarith only [h0, h2843, h2935, h2943, h2944, h2945, h2947, h4, hlam]
                            · rcases h2bigk with h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2843, h2944, h4, hc12, hc23, hlam, hphi, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h4, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2843, h2943, h2944, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2670, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h0, hlam, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2933, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h0, h2943, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2936, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                rcases p2949_3 (m.d 0 2) (by simp) with h2963 | h2963
                                · linarith only [h2963, h4, hlam]
                                · linarith only [h2669, h2963, hlam]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2843, h2944, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2669, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2935, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2943, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2945, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h0, h2935, h2943, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2935, h2943, h2945, hc34, hc45, hlam, hphi, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2944, hlam, p2949_0]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [h2943, h2945, hc34, hc45, hlam, hphi, p2949_1]
                              · have p2949_0 := h2949c.1
                                have p2949_1 := h2949c.2.1
                                have p2949_2 := h2949c.2.2.1
                                have p2949_3 := h2949c.2.2.2
                                linarith only [hlam, p2949_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2977 | h2977
                          · linarith only [h0, h2935, h2944, h2977, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2979 | h2979
                            · linarith only [h0, h2935, h2943, h2944, h2977, h2979, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h2935, h2943, h2944, h2979, h4, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h2842, h2935, h2943, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h2842, h2843, h2938, hc13, hc35, hlam, hphi]
            · linarith only [h2669, h2935, h4, hc12, hc23, hlam, hphi]
    · linarith only [h2669, h2842, h4, hlam]

end R2N4
