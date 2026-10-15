import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1948 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1949 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 1 2 3 (by decide) (by decide) with h2487 | h2487
  · linarith only [h0, h1947, h2487, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2489 | h2489
    · linarith only [h0, h1304, h2489, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2491 | h2491
      · linarith only [h0, h1819, h2491, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2493 | h2493
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2494 | h2494
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2495 | h2495
            · linarith only [h0, h1304, h1949, h2, h2495, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2497 | h2497
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2498 | h2498
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2499 | h2499
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2500 | h2500
                    · linarith only [h0, h1, h1304, h1949, h2493, h2500, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        rcases p2502_3 (m.d 0 1) (by simp) with h2504 | h2504
                        · rcases p2502_3 (m.d 0 2) (by simp) with h2505 | h2505
                          · linarith only [h0, h2505, hlam]
                          · rcases p2502_3 (m.d 0 3) (by simp) with h2507 | h2507
                            · linarith only [h1, h2507, hlam]
                            · linarith only [h2507, h4, hlam]
                        · linarith only [h0, h2504, hlam]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1947, hc34, hlam, hphi, ht0b, ht45, ht5b, p2502_1, u0elo0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        rcases p2502_3 (m.d 0 1) (by simp) with h2512 | h2512
                        · rcases p2502_3 (m.d 0 2) (by simp) with h2513 | h2513
                          · linarith only [h0, h2513, hlam]
                          · rcases p2502_3 (m.d 0 3) (by simp) with h2515 | h2515
                            · linarith only [h1, h2515, hlam]
                            · linarith only [h1947, h2515, hlam]
                        · linarith only [h2, h2512, hlam]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        rcases p2502_3 (m.d 0 1) (by simp) with h2519 | h2519
                        · rcases p2502_3 (m.d 0 2) (by simp) with h2520 | h2520
                          · linarith only [h0, h2520, hlam]
                          · rcases p2502_3 (m.d 0 3) (by simp) with h2522 | h2522
                            · linarith only [h1, h2522, hlam]
                            · linarith only [h1948, h2522, hlam]
                        · linarith only [h2519, h3, hlam]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h0, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h4, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1304, hlam, p2502_1]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1819, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1, hlam, p2502_1]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        rcases p2502_3 (m.d 0 1) (by simp) with h2532 | h2532
                        · rcases p2502_3 (m.d 0 2) (by simp) with h2533 | h2533
                          · linarith only [h2533, h4, hlam]
                          · rcases p2502_3 (m.d 0 3) (by simp) with h2535 | h2535
                            · rcases p2502_3 (m.d 0 4) (by simp) with h2536 | h2536
                              · linarith only [h1947, h2536, hlam]
                              · linarith only [h1304, h2536, hlam]
                            · linarith only [h2535, h4, hlam]
                        · linarith only [h0, h2532, hlam]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        rcases p2502_3 (m.d 0 1) (by simp) with h2542 | h2542
                        · rcases p2502_3 (m.d 0 2) (by simp) with h2543 | h2543
                          · linarith only [h2543, h4, hlam]
                          · rcases p2502_3 (m.d 0 3) (by simp) with h2545 | h2545
                            · rcases p2502_3 (m.d 0 4) (by simp) with h2546 | h2546
                              · linarith only [h1947, h2546, hlam]
                              · rcases p2502_3 (m.d 0 5) (by simp) with h2548 | h2548
                                · linarith only [h1948, h2548, hlam]
                                · linarith only [h1949, h2548, hlam]
                            · linarith only [h1947, h2545, hlam]
                        · linarith only [h2, h2542, hlam]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        rcases p2502_3 (m.d 0 1) (by simp) with h2553 | h2553
                        · rcases p2502_3 (m.d 0 2) (by simp) with h2554 | h2554
                          · linarith only [h2554, h4, hlam]
                          · rcases p2502_3 (m.d 0 3) (by simp) with h2556 | h2556
                            · rcases p2502_3 (m.d 0 4) (by simp) with h2557 | h2557
                              · linarith only [h1947, h2557, hlam]
                              · rcases p2502_3 (m.d 0 5) (by simp) with h2559 | h2559
                                · linarith only [h1948, h2559, hlam]
                                · rcases h0emin with h2561 | h2561 | h2561 | h2561 | h2561
                                  · rcases h1bigk with h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      rcases p2562_3 (m.d 0 1) (by simp) with h2564 | h2564
                                      · rcases p2562_3 (m.d 1 2) (by simp) with h2565 | h2565
                                        · linarith only [h2565, hlam, p2562_0]
                                        · rcases p2562_3 (m.d 1 3) (by simp) with h2567 | h2567
                                          · linarith only [h1, h2567, hlam]
                                          · linarith only [h2487, h2567, hlam]
                                      · linarith only [h2564, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2494, h2500, hc34, hlam, hphi, ht0b, ht45, ht5b, p2562_1, u0elo0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      rcases p2562_3 (m.d 0 1) (by simp) with h2572 | h2572
                                      · rcases p2562_3 (m.d 1 2) (by simp) with h2573 | h2573
                                        · linarith only [h0, h2573, hlam]
                                        · rcases p2562_3 (m.d 1 3) (by simp) with h2575 | h2575
                                          · linarith only [h1, h2575, hlam]
                                          · linarith only [h2493, h2575, hlam]
                                      · linarith only [h2572, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      rcases p2562_3 (m.d 0 1) (by simp) with h2579 | h2579
                                      · rcases p2562_3 (m.d 1 2) (by simp) with h2580 | h2580
                                        · linarith only [h0, h2580, hlam]
                                        · rcases p2562_3 (m.d 1 3) (by simp) with h2582 | h2582
                                          · linarith only [h1, h2582, hlam]
                                          · linarith only [h2494, h2582, hlam]
                                      · linarith only [h2579, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h0, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2487, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2489, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2491, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h1, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2562_1, u0elo0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h1, hc14, hlam, hphi, ht0b, ht45, ht5b, p2562_1, u0elo0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2562_1, u0elo0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2562_1, u0elo0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2493, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2495, hlam, p2562_1]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h3, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2562_1, u0elo0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h2494, hlam, p2562_0]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p2502_1, p2562_1, u0elo2]
                                    · have p2562_0 := h2562c.1
                                      have p2562_1 := h2562c.2.1
                                      have p2562_2 := h2562c.2.2.1
                                      have p2562_3 := h2562c.2.2.2
                                      linarith only [hlam, p2562_0]
                                  · linarith only [h1304, h1949, h2499, h2561, hc24, hlam, ht01, ht12]
                                  · rcases h1bigk with h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c | h2607c
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      rcases p2607_3 (m.d 0 1) (by simp) with h2609 | h2609
                                      · rcases p2607_3 (m.d 1 2) (by simp) with h2610 | h2610
                                        · linarith only [h2610, hlam, p2607_0]
                                        · rcases p2607_3 (m.d 1 3) (by simp) with h2612 | h2612
                                          · linarith only [h1, h2612, hlam]
                                          · linarith only [h2487, h2612, hlam]
                                      · linarith only [h2609, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2493, hc34, hlam, hphi, ht0b, ht45, ht5b, p2607_1, u0elo0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      rcases p2607_3 (m.d 0 1) (by simp) with h2617 | h2617
                                      · rcases p2607_3 (m.d 1 2) (by simp) with h2618 | h2618
                                        · linarith only [h0, h2618, hlam]
                                        · rcases p2607_3 (m.d 1 3) (by simp) with h2620 | h2620
                                          · linarith only [h1, h2620, hlam]
                                          · linarith only [h2493, h2620, hlam]
                                      · linarith only [h2617, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      rcases p2607_3 (m.d 0 1) (by simp) with h2624 | h2624
                                      · rcases p2607_3 (m.d 1 2) (by simp) with h2625 | h2625
                                        · linarith only [h0, h2625, hlam]
                                        · rcases p2607_3 (m.d 1 3) (by simp) with h2627 | h2627
                                          · linarith only [h1, h2627, hlam]
                                          · linarith only [h2494, h2627, hlam]
                                      · linarith only [h2624, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h0, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2487, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2489, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2491, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h1, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2607_1, u0elo0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h1, h2489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2607_1, u0elo0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2607_1, u0elo0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2607_1, u0elo0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2493, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2495, hlam, p2607_1]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h3, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2607_1, u0elo0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h2494, hlam, p2607_0]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p2502_1, p2607_1, u0elo2]
                                    · have p2607_0 := h2607c.1
                                      have p2607_1 := h2607c.2.1
                                      have p2607_2 := h2607c.2.2.1
                                      have p2607_3 := h2607c.2.2.2
                                      linarith only [hlam, p2607_0]
                                  · linarith only [h1949, h2497, h2499, h2561, hc23, hlam, ht01, ht12]
                                  · linarith only [h1, h2561, hlam, p2502_1, u0elo0]
                            · linarith only [h1948, h2556, hlam]
                        · linarith only [h2553, h3, hlam]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h2, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h0, h1949, h2497, h2499, hc12, hc23, hlam, hphi, p2502_1]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1947, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1949, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h3, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h0, h1949, h2497, h2499, hc12, hc23, hlam, hphi, p2502_1]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h1948, hlam, p2502_0]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [h0, h1304, h1949, h2497, h2499, hc12, hc23, hlam, hphi, p2502_1]
                      · have p2502_0 := h2502c.1
                        have p2502_1 := h2502c.2.1
                        have p2502_2 := h2502c.2.2.1
                        have p2502_3 := h2502c.2.2.2
                        linarith only [hlam, p2502_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2665 | h2665
                    · linarith only [h0, h1304, h2499, h2665, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2669 | h2669
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2670 | h2670
                          · linarith only [h0, h2670, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2672 | h2672
                            · linarith only [h1, h2672, hlam]
                            · linarith only [h2672, h4, hlam]
                        · linarith only [h0, h2669, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1947, hc34, hlam, hphi, ht0b, ht45, ht5b, p2667_1, u0elo0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2677 | h2677
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2678 | h2678
                          · linarith only [h0, h2678, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2680 | h2680
                            · linarith only [h1, h2680, hlam]
                            · linarith only [h1947, h2680, hlam]
                        · linarith only [h2, h2677, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2684 | h2684
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2685 | h2685
                          · linarith only [h0, h2685, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2687 | h2687
                            · linarith only [h1, h2687, hlam]
                            · linarith only [h1948, h2687, hlam]
                        · linarith only [h2684, h3, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h0, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h4, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1304, hlam, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1819, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1, hlam, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2697 | h2697
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2698 | h2698
                          · linarith only [h2698, h4, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2700 | h2700
                            · rcases p2667_3 (m.d 0 4) (by simp) with h2701 | h2701
                              · linarith only [h1947, h2701, hlam]
                              · linarith only [h1304, h2701, hlam]
                            · linarith only [h2700, h4, hlam]
                        · linarith only [h0, h2697, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2707 | h2707
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2708 | h2708
                          · linarith only [h2708, h4, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2710 | h2710
                            · rcases p2667_3 (m.d 0 4) (by simp) with h2711 | h2711
                              · linarith only [h1947, h2711, hlam]
                              · rcases p2667_3 (m.d 0 5) (by simp) with h2713 | h2713
                                · linarith only [h1948, h2713, hlam]
                                · linarith only [h1949, h2713, hlam]
                            · linarith only [h1947, h2710, hlam]
                        · linarith only [h2, h2707, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2718 | h2718
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2719 | h2719
                          · linarith only [h2719, h4, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2721 | h2721
                            · rcases p2667_3 (m.d 0 4) (by simp) with h2722 | h2722
                              · linarith only [h1947, h2722, hlam]
                              · rcases p2667_3 (m.d 0 5) (by simp) with h2724 | h2724
                                · linarith only [h1948, h2724, hlam]
                                · rcases h0emin with h2726 | h2726 | h2726 | h2726 | h2726
                                  · rcases h1bigk with h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      rcases p2727_3 (m.d 0 1) (by simp) with h2729 | h2729
                                      · rcases p2727_3 (m.d 1 2) (by simp) with h2730 | h2730
                                        · linarith only [h2730, hlam, p2727_0]
                                        · rcases p2727_3 (m.d 1 3) (by simp) with h2732 | h2732
                                          · linarith only [h1, h2732, hlam]
                                          · linarith only [h2487, h2732, hlam]
                                      · linarith only [h2729, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2494, h2665, hc34, hlam, hphi, ht0b, ht45, ht5b, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      rcases p2727_3 (m.d 0 1) (by simp) with h2737 | h2737
                                      · rcases p2727_3 (m.d 1 2) (by simp) with h2738 | h2738
                                        · linarith only [h0, h2738, hlam]
                                        · rcases p2727_3 (m.d 1 3) (by simp) with h2740 | h2740
                                          · linarith only [h1, h2740, hlam]
                                          · linarith only [h2493, h2740, hlam]
                                      · linarith only [h2737, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      rcases p2727_3 (m.d 0 1) (by simp) with h2744 | h2744
                                      · rcases p2727_3 (m.d 1 2) (by simp) with h2745 | h2745
                                        · linarith only [h0, h2745, hlam]
                                        · rcases p2727_3 (m.d 1 3) (by simp) with h2747 | h2747
                                          · linarith only [h1, h2747, hlam]
                                          · linarith only [h2494, h2747, hlam]
                                      · linarith only [h2744, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h0, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2487, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2489, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2491, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h1, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h1, h2489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2493, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2495, hlam, p2727_1]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h3, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h2494, hlam, p2727_0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [h1, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p2667_1, p2727_1, u0elo0]
                                    · have p2727_0 := h2727c.1
                                      have p2727_1 := h2727c.2.1
                                      have p2727_2 := h2727c.2.2.1
                                      have p2727_3 := h2727c.2.2.2
                                      linarith only [hlam, p2727_0]
                                  · linarith only [h1304, h2499, h2726, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · rcases h1bigk with h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      rcases p2772_3 (m.d 0 1) (by simp) with h2774 | h2774
                                      · rcases p2772_3 (m.d 1 2) (by simp) with h2775 | h2775
                                        · linarith only [h2775, hlam, p2772_0]
                                        · rcases p2772_3 (m.d 1 3) (by simp) with h2777 | h2777
                                          · linarith only [h1, h2777, hlam]
                                          · linarith only [h2487, h2777, hlam]
                                      · linarith only [h2774, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2493, hc34, hlam, hphi, ht0b, ht45, ht5b, p2772_1, u0elo0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      rcases p2772_3 (m.d 0 1) (by simp) with h2782 | h2782
                                      · rcases p2772_3 (m.d 1 2) (by simp) with h2783 | h2783
                                        · linarith only [h0, h2783, hlam]
                                        · rcases p2772_3 (m.d 1 3) (by simp) with h2785 | h2785
                                          · linarith only [h1, h2785, hlam]
                                          · linarith only [h2493, h2785, hlam]
                                      · linarith only [h2782, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      rcases p2772_3 (m.d 0 1) (by simp) with h2789 | h2789
                                      · rcases p2772_3 (m.d 1 2) (by simp) with h2790 | h2790
                                        · linarith only [h0, h2790, hlam]
                                        · rcases p2772_3 (m.d 1 3) (by simp) with h2792 | h2792
                                          · linarith only [h1, h2792, hlam]
                                          · linarith only [h2494, h2792, hlam]
                                      · linarith only [h2789, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h0, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2487, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2489, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2491, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h1, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2772_1, u0elo0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h1, h2489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2772_1, u0elo0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2772_1, u0elo0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2772_1, u0elo0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2493, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2495, hlam, p2772_1]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h3, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2772_1, u0elo0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h2494, hlam, p2772_0]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p2667_1, p2772_1, u0elo2]
                                    · have p2772_0 := h2772c.1
                                      have p2772_1 := h2772c.2.1
                                      have p2772_2 := h2772c.2.2.1
                                      have p2772_3 := h2772c.2.2.2
                                      linarith only [hlam, p2772_0]
                                  · linarith only [h1, h1949, h2726, hlam, p2667_1, u0elo0]
                                  · linarith only [h1, h2726, hlam, p2667_1, u0elo0]
                            · linarith only [h1948, h2721, hlam]
                        · linarith only [h2718, h3, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h0, h1304, h2499, hc12, hc45, hlam, hphi, ht23, ht34, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1947, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1949, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h3, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2826 | h2826
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2827 | h2827
                          · linarith only [h1819, h2827, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2829 | h2829
                            · rcases p2667_3 (m.d 0 4) (by simp) with h2830 | h2830
                              · linarith only [h1949, h2830, hlam]
                              · linarith only [h1304, h2830, hlam]
                            · linarith only [h2829, h4, hlam]
                        · linarith only [h0, h2826, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1948, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2836 | h2836
                        · rcases p2667_3 (m.d 0 2) (by simp) with h2837 | h2837
                          · linarith only [h1819, h2837, hlam]
                          · rcases p2667_3 (m.d 0 3) (by simp) with h2839 | h2839
                            · rcases p2667_3 (m.d 0 4) (by simp) with h2840 | h2840
                              · linarith only [h1949, h2840, hlam]
                              · rcases p2667_3 (m.d 0 5) (by simp) with h2842 | h2842
                                · rcases h0emin with h2843 | h2843 | h2843 | h2843 | h2843
                                  · rcases h1bigk with h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      rcases p2844_3 (m.d 0 1) (by simp) with h2846 | h2846
                                      · rcases p2844_3 (m.d 1 2) (by simp) with h2847 | h2847
                                        · linarith only [h2847, hlam, p2844_0]
                                        · rcases p2844_3 (m.d 1 3) (by simp) with h2849 | h2849
                                          · linarith only [h1, h2849, hlam]
                                          · linarith only [h2487, h2849, hlam]
                                      · linarith only [h2846, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2493, hc34, hlam, hphi, ht0b, ht45, ht5b, p2844_1, u0elo0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      rcases p2844_3 (m.d 0 1) (by simp) with h2854 | h2854
                                      · rcases p2844_3 (m.d 1 2) (by simp) with h2855 | h2855
                                        · linarith only [h0, h2855, hlam]
                                        · rcases p2844_3 (m.d 1 3) (by simp) with h2857 | h2857
                                          · linarith only [h1, h2857, hlam]
                                          · linarith only [h2493, h2857, hlam]
                                      · linarith only [h2854, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      rcases p2844_3 (m.d 0 1) (by simp) with h2861 | h2861
                                      · rcases p2844_3 (m.d 1 2) (by simp) with h2862 | h2862
                                        · linarith only [h0, h2862, hlam]
                                        · rcases p2844_3 (m.d 1 3) (by simp) with h2864 | h2864
                                          · linarith only [h1, h2864, hlam]
                                          · linarith only [h2494, h2864, hlam]
                                      · linarith only [h2861, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h0, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2487, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2489, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2491, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h1, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2844_1, u0elo0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h1, h2489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2844_1, u0elo0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2844_1, u0elo0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2667_1, p2844_1, u0elo4]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2493, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2495, hlam, p2844_1]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h3, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2844_1, u0elo0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h2494, hlam, p2844_0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [h1, h2494, hc14, hlam, hphi, ht0b, ht45, ht5b, p2844_1, u0elo0]
                                    · have p2844_0 := h2844c.1
                                      have p2844_1 := h2844c.2.1
                                      have p2844_2 := h2844c.2.2.1
                                      have p2844_3 := h2844c.2.2.2
                                      linarith only [hlam, p2844_0]
                                  · linarith only [h1304, h2499, h2843, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · rcases h1bigk with h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      rcases p2889_3 (m.d 0 1) (by simp) with h2891 | h2891
                                      · rcases p2889_3 (m.d 1 2) (by simp) with h2892 | h2892
                                        · linarith only [h2892, hlam, p2889_0]
                                        · rcases p2889_3 (m.d 1 3) (by simp) with h2894 | h2894
                                          · linarith only [h1, h2894, hlam]
                                          · linarith only [h2487, h2894, hlam]
                                      · linarith only [h2891, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2493, hc34, hlam, hphi, ht0b, ht45, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      rcases p2889_3 (m.d 0 1) (by simp) with h2899 | h2899
                                      · rcases p2889_3 (m.d 1 2) (by simp) with h2900 | h2900
                                        · linarith only [h0, h2900, hlam]
                                        · rcases p2889_3 (m.d 1 3) (by simp) with h2902 | h2902
                                          · linarith only [h1, h2902, hlam]
                                          · linarith only [h2493, h2902, hlam]
                                      · linarith only [h2899, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      rcases p2889_3 (m.d 0 1) (by simp) with h2906 | h2906
                                      · rcases p2889_3 (m.d 1 2) (by simp) with h2907 | h2907
                                        · linarith only [h0, h2907, hlam]
                                        · rcases p2889_3 (m.d 1 3) (by simp) with h2909 | h2909
                                          · linarith only [h1, h2909, hlam]
                                          · linarith only [h2494, h2909, hlam]
                                      · linarith only [h2906, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h0, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2487, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2489, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2491, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h1, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h1, h2489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2493, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2495, hlam, p2889_1]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h3, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h2494, hlam, p2889_0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [h1, h2494, hc14, hlam, hphi, ht0b, ht45, ht5b, p2889_1, u0elo0]
                                    · have p2889_0 := h2889c.1
                                      have p2889_1 := h2889c.2.1
                                      have p2889_2 := h2889c.2.2.1
                                      have p2889_3 := h2889c.2.2.2
                                      linarith only [hlam, p2889_0]
                                  · linarith only [h1, h1948, h2843, hlam, p2667_1, u0elo0]
                                  · rcases h1bigk with h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c | h2934c
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      rcases p2934_3 (m.d 0 1) (by simp) with h2936 | h2936
                                      · rcases p2934_3 (m.d 1 2) (by simp) with h2937 | h2937
                                        · linarith only [h2937, hlam, p2934_0]
                                        · rcases p2934_3 (m.d 1 3) (by simp) with h2939 | h2939
                                          · linarith only [h1, h2939, hlam]
                                          · linarith only [h2487, h2939, hlam]
                                      · linarith only [h2936, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2493, hc34, hlam, hphi, ht0b, ht45, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      rcases p2934_3 (m.d 0 1) (by simp) with h2944 | h2944
                                      · rcases p2934_3 (m.d 1 2) (by simp) with h2945 | h2945
                                        · linarith only [h0, h2945, hlam]
                                        · rcases p2934_3 (m.d 1 3) (by simp) with h2947 | h2947
                                          · linarith only [h1, h2947, hlam]
                                          · linarith only [h2493, h2947, hlam]
                                      · linarith only [h2944, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      rcases p2934_3 (m.d 0 1) (by simp) with h2951 | h2951
                                      · rcases p2934_3 (m.d 1 2) (by simp) with h2952 | h2952
                                        · linarith only [h0, h2952, hlam]
                                        · rcases p2934_3 (m.d 1 3) (by simp) with h2954 | h2954
                                          · linarith only [h1, h2954, hlam]
                                          · linarith only [h2494, h2954, hlam]
                                      · linarith only [h2951, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h0, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2487, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2489, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2491, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h1, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h1, h2489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2493, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2495, hlam, p2934_1]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h3, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h2494, hlam, p2934_0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [h1, h2494, hc14, hlam, hphi, ht0b, ht45, ht5b, p2934_1, u0elo0]
                                    · have p2934_0 := h2934c.1
                                      have p2934_1 := h2934c.2.1
                                      have p2934_2 := h2934c.2.2.1
                                      have p2934_3 := h2934c.2.2.2
                                      linarith only [hlam, p2934_0]
                                · linarith only [h1949, h2842, hlam]
                            · linarith only [h1947, h2839, hlam]
                        · linarith only [h2, h2836, hlam]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                · linarith only [h1948, h2498, h4, hlam]
              · linarith only [h1947, h2497, h4, hlam]
          · linarith only [h1948, h2493, h2494, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2985 | h2985
          · linarith only [h1, h1947, h2493, h2985, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2987 | h2987
            · linarith only [h1949, h2, h2987, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2989 | h2989
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2990 | h2990
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2991 | h2991
                  · linarith only [h1947, h1949, h2487, h2493, h2991, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2993 | h2993
                    · linarith only [h0, h1304, h1947, h2991, h2993, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases h0bigk with h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        rcases p2995_3 (m.d 0 1) (by simp) with h2997 | h2997
                        · rcases p2995_3 (m.d 0 2) (by simp) with h2998 | h2998
                          · linarith only [h0, h2998, hlam]
                          · rcases p2995_3 (m.d 0 3) (by simp) with h3000 | h3000
                            · linarith only [h1, h3000, hlam]
                            · linarith only [h3000, h4, hlam]
                        · linarith only [h0, h2997, hlam]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1948, h2985, h2987, hc14, hlam, hphi, ht0b, ht45, ht5b, p2995_1, u0elo0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1947, h2487, h2493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2995_1, u0elo0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1947, h1949, h2487, h2493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2995_1, u0elo0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h0, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h4, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1304, hlam, p2995_1]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1819, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1, hlam, p2995_1]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        rcases p2995_3 (m.d 0 1) (by simp) with h3013 | h3013
                        · rcases p2995_3 (m.d 0 2) (by simp) with h3014 | h3014
                          · linarith only [h3014, h4, hlam]
                          · rcases p2995_3 (m.d 0 3) (by simp) with h3016 | h3016
                            · rcases p2995_3 (m.d 0 4) (by simp) with h3017 | h3017
                              · linarith only [h1947, h3017, hlam]
                              · linarith only [h1304, h3017, hlam]
                            · linarith only [h3016, h4, hlam]
                        · linarith only [h0, h3013, hlam]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1947, h2487, h2493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2995_1, u0elo2]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1, h1947, h1949, h2487, h2493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2995_1, u0elo0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h2, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h0, h1304, h2991, hc12, hc45, hlam, hphi, ht23, ht34, p2995_1]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1947, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1949, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h3, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        rcases p2995_3 (m.d 0 1) (by simp) with h3031 | h3031
                        · rcases p2995_3 (m.d 0 2) (by simp) with h3032 | h3032
                          · linarith only [h1819, h3032, hlam]
                          · rcases p2995_3 (m.d 0 3) (by simp) with h3034 | h3034
                            · rcases p2995_3 (m.d 0 4) (by simp) with h3035 | h3035
                              · linarith only [h1949, h3035, hlam]
                              · linarith only [h1304, h3035, hlam]
                            · linarith only [h3034, h4, hlam]
                        · linarith only [h0, h3031, hlam]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1948, hlam, p2995_0]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [h1947, h2487, h2493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2995_1, u0elo4]
                      · have p2995_0 := h2995c.1
                        have p2995_1 := h2995c.2.1
                        have p2995_2 := h2995c.2.2.1
                        have p2995_3 := h2995c.2.2.2
                        linarith only [hlam, p2995_0]
                · linarith only [h1947, h2487, h2493, h2990, h4, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1947, h2989, h4, hlam]

set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1948 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 4 5 (by decide) (by decide) with h1949 | h1949
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h1948 h1949
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h1948 h1949

set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1948 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 4 5 (by decide) (by decide) with h3045 | h3045
  · linarith only [h1947, h1948, h3045, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3047 | h3047
    · linarith only [h0, h1947, h3047, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3049 | h3049
      · linarith only [h0, h1304, h3049, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3051 | h3051
        · linarith only [h0, h1819, h3051, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3053 | h3053
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3054 | h3054
            · linarith only [h1, h1948, h3054, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3056 | h3056
              · linarith only [h2, h3045, h3056, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3058 | h3058
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3059 | h3059
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3060 | h3060
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3061 | h3061
                      · linarith only [h0, h1, h1304, h3045, h3053, h3061, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c | h3063c
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          rcases p3063_3 (m.d 0 1) (by simp) with h3065 | h3065
                          · rcases p3063_3 (m.d 0 2) (by simp) with h3066 | h3066
                            · linarith only [h0, h3066, hlam]
                            · rcases p3063_3 (m.d 0 3) (by simp) with h3068 | h3068
                              · linarith only [h1, h3068, hlam]
                              · linarith only [h3068, h4, hlam]
                          · linarith only [h0, h3065, hlam]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3063_1, u0elo0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          rcases p3063_3 (m.d 0 1) (by simp) with h3073 | h3073
                          · rcases p3063_3 (m.d 0 2) (by simp) with h3074 | h3074
                            · linarith only [h0, h3074, hlam]
                            · rcases p3063_3 (m.d 0 3) (by simp) with h3076 | h3076
                              · linarith only [h1, h3076, hlam]
                              · linarith only [h1947, h3076, hlam]
                          · linarith only [h2, h3073, hlam]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1, h1948, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3063_1, u0elo0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h0, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h4, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1304, hlam, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1819, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1, hlam, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h0, h1948, h3058, h3060, h3061, hc12, hc23, hlam, hphi, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h0, h1304, h1948, h3058, h3060, h3061, hc12, hc23, hlam, hphi, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1948, hlam, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h2, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h0, h1947, h1948, h3058, h3060, h3061, hc12, hc23, hlam, hphi, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1947, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h3045, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h3, hlam, p3063_0]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h0, h1948, h3058, h3060, h3061, hc12, hc23, hlam, hphi, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1, h1948, h3053, h3058, h3060, h3061, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [h1948, h2, h3049, h3058, h3060, h3061, hc12, hc23, hlam, hphi, p3063_1]
                        · have p3063_0 := h3063c.1
                          have p3063_1 := h3063c.2.1
                          have p3063_2 := h3063c.2.2.1
                          have p3063_3 := h3063c.2.2.2
                          linarith only [hlam, p3063_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3101 | h3101
                      · linarith only [h1, h3053, h3060, h3101, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c | h3103c
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          rcases p3103_3 (m.d 0 1) (by simp) with h3105 | h3105
                          · rcases p3103_3 (m.d 0 2) (by simp) with h3106 | h3106
                            · linarith only [h0, h3106, hlam]
                            · rcases p3103_3 (m.d 0 3) (by simp) with h3108 | h3108
                              · linarith only [h1, h3108, hlam]
                              · linarith only [h3108, h4, hlam]
                          · linarith only [h0, h3105, hlam]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3103_1, u0elo0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          rcases p3103_3 (m.d 0 1) (by simp) with h3113 | h3113
                          · rcases p3103_3 (m.d 0 2) (by simp) with h3114 | h3114
                            · linarith only [h0, h3114, hlam]
                            · rcases p3103_3 (m.d 0 3) (by simp) with h3116 | h3116
                              · linarith only [h1, h3116, hlam]
                              · linarith only [h1947, h3116, hlam]
                          · linarith only [h2, h3113, hlam]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1, h1948, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3103_1, u0elo0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h0, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h4, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1304, hlam, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1819, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1, hlam, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h0, h1948, h3059, hc12, hc25, hlam, hphi, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1948, h2, h3049, h3059, hc12, hc25, hlam, hphi, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1948, hlam, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h2, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h0, h1304, h3060, hc12, hc45, hlam, hphi, ht23, ht34, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h1947, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h3045, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h3, hlam, p3103_0]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h0, h1948, h3059, hc12, hc23, hlam, hphi, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h0, h1948, h3059, h4, hc12, hc23, hlam, hphi, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [h0, h1304, h1948, h3059, hc12, hc23, hlam, hphi, p3103_1]
                        · have p3103_0 := h3103c.1
                          have p3103_1 := h3103c.2.1
                          have p3103_2 := h3103c.2.2.1
                          have p3103_3 := h3103c.2.2.2
                          linarith only [hlam, p3103_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3141 | h3141
                    · linarith only [h0, h1304, h3045, h3058, h3059, h3141, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3143 | h3143
                      · linarith only [h0, h1, h1304, h3053, h3141, h3143, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          rcases p3145_3 (m.d 0 1) (by simp) with h3147 | h3147
                          · rcases p3145_3 (m.d 0 2) (by simp) with h3148 | h3148
                            · linarith only [h0, h3148, hlam]
                            · rcases p3145_3 (m.d 0 3) (by simp) with h3150 | h3150
                              · linarith only [h1, h3150, hlam]
                              · linarith only [h3150, h4, hlam]
                          · linarith only [h0, h3147, hlam]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3145_1, u0elo0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          rcases p3145_3 (m.d 0 1) (by simp) with h3155 | h3155
                          · rcases p3145_3 (m.d 0 2) (by simp) with h3156 | h3156
                            · linarith only [h0, h3156, hlam]
                            · rcases p3145_3 (m.d 0 3) (by simp) with h3158 | h3158
                              · linarith only [h1, h3158, hlam]
                              · linarith only [h1947, h3158, hlam]
                          · linarith only [h2, h3155, hlam]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1, h1948, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3145_1, u0elo0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h0, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h4, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1304, hlam, p3145_1]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1819, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1, hlam, p3145_1]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h0, h3059, h3143, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3145_1]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h0, h1304, h3059, h3143, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3145_1]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1948, hlam, p3145_1]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h2, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h0, h1947, h3059, h3143, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3145_1]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1947, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h3045, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h3, hlam, p3145_0]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          rcases p3145_3 (m.d 0 1) (by simp) with h3179 | h3179
                          · rcases p3145_3 (m.d 0 2) (by simp) with h3180 | h3180
                            · linarith only [h1819, h3180, hlam]
                            · rcases p3145_3 (m.d 0 3) (by simp) with h3182 | h3182
                              · linarith only [h1948, h3182, hlam]
                              · linarith only [h3182, h4, hlam]
                          · linarith only [h0, h3179, hlam]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [h1, h3053, hc34, hlam, hphi, ht0b, ht45, ht5b, p3145_1, u0elo4]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          rcases p3145_3 (m.d 0 1) (by simp) with h3187 | h3187
                          · rcases p3145_3 (m.d 0 2) (by simp) with h3188 | h3188
                            · linarith only [h1819, h3188, hlam]
                            · rcases p3145_3 (m.d 0 3) (by simp) with h3190 | h3190
                              · linarith only [h1948, h3190, hlam]
                              · linarith only [h1947, h3190, hlam]
                          · linarith only [h2, h3187, hlam]
                        · have p3145_0 := h3145c.1
                          have p3145_1 := h3145c.2.1
                          have p3145_2 := h3145c.2.2.1
                          have p3145_3 := h3145c.2.2.2
                          linarith only [hlam, p3145_0]
                · linarith only [h1, h3053, h3058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h1947, h1948, h3047, h3053, hc12, hc35, hlam, hphi, ht23]

set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 3 5 (by decide) (by decide) with h1948 | h1948
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h1948
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h1948

end R2N4
