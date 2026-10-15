import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8110000 in
set_option maxHeartbeats 8110000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s8_x1_x0 (m : N7Model)
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
    (h2520 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h2521 | h2521
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2522 | h2522
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2523 | h2523
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2524 | h2524
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2525 | h2525
          · linarith only [h2, h2525, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2527 | h2527
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2528 | h2528
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2529 | h2529
                · linarith only [h2, h2521, h2529, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2531 | h2531
                  · linarith only [h0, h2527, h2531, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c | h2533c
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h0, h2520, h2528, h2531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2533_1]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2536 | h2536
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2537 | h2537
                        · linarith only [h0, h2537, hlam]
                        · linarith only [h2537, h4, hlam]
                      · linarith only [h1, h2536, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2541 | h2541
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2542 | h2542
                        · linarith only [h0, h2542, hlam]
                        · linarith only [h2542, h5, hlam]
                      · linarith only [h2, h2541, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2546 | h2546
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2547 | h2547
                        · linarith only [h0, h2547, hlam]
                        · linarith only [h2547, h6, hlam]
                      · linarith only [h2546, h3, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h0, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2553 | h2553
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2554 | h2554
                        · rcases p2533_3 (m.d 0 3) (by simp) with h2555 | h2555
                          · linarith only [h2555, h4, hlam]
                          · rcases p2533_3 (m.d 0 4) (by simp) with h2557 | h2557
                            · linarith only [h2557, h5, hlam]
                            · rcases p2533_3 (m.d 0 5) (by simp) with h2559 | h2559
                              · linarith only [h2559, h6, hlam]
                              · rcases h2bigk with h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h0, h2520, h2528, h2531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  rcases p2561_3 (m.d 0 2) (by simp) with h2564 | h2564
                                  · rcases p2561_3 (m.d 1 2) (by simp) with h2565 | h2565
                                    · linarith only [h0, h2565, hlam]
                                    · linarith only [h2520, h2565, hlam]
                                  · linarith only [h2564, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  rcases p2561_3 (m.d 0 2) (by simp) with h2569 | h2569
                                  · rcases p2561_3 (m.d 1 2) (by simp) with h2570 | h2570
                                    · linarith only [h0, h2570, hlam]
                                    · linarith only [h2521, h2570, hlam]
                                  · linarith only [h2569, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  rcases p2561_3 (m.d 0 2) (by simp) with h2574 | h2574
                                  · rcases p2561_3 (m.d 1 2) (by simp) with h2575 | h2575
                                    · linarith only [h0, h2575, hlam]
                                    · linarith only [h2522, h2575, hlam]
                                  · linarith only [h2574, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h0, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h0, h2528, h2531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  rcases p2561_3 (m.d 0 2) (by simp) with h2582 | h2582
                                  · rcases p2561_3 (m.d 1 2) (by simp) with h2583 | h2583
                                    · rcases p2561_3 (m.d 2 3) (by simp) with h2584 | h2584
                                      · linarith only [h2520, h2584, hlam]
                                      · linarith only [h2527, h2584, hlam]
                                    · linarith only [h2583, hlam, p2561_0]
                                  · linarith only [h2582, h5, hlam]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  rcases p2561_3 (m.d 0 2) (by simp) with h2589 | h2589
                                  · rcases p2561_3 (m.d 1 2) (by simp) with h2590 | h2590
                                    · rcases p2561_3 (m.d 2 3) (by simp) with h2591 | h2591
                                      · linarith only [h2520, h2591, hlam]
                                      · linarith only [h2528, h2591, hlam]
                                    · linarith only [h2590, hlam, p2561_0]
                                  · linarith only [h2589, h6, hlam]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h4, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h2520, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h1, h2520, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2533_1, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h0, h1, h2520, hc01, hc25, hlam, hphi, ht0b, ht5b, p2533_1, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h5, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h2521, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h2527, hlam, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h2529, hlam, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h6, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h2522, hlam, p2561_0]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h2528, hlam, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [h0, h2527, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2533_1, p2561_1]
                                · have p2561_0 := h2561c.1
                                  have p2561_1 := h2561c.2.1
                                  have p2561_2 := h2561c.2.2.1
                                  have p2561_3 := h2561c.2.2.2
                                  linarith only [hlam, p2561_0]
                        · linarith only [h2554, h4, hlam]
                      · linarith only [h1, h2553, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2613 | h2613
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2614 | h2614
                        · rcases p2533_3 (m.d 0 3) (by simp) with h2615 | h2615
                          · linarith only [h2615, h4, hlam]
                          · linarith only [h2615, h7, hlam]
                        · linarith only [h2614, h5, hlam]
                      · linarith only [h2, h2613, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2620 | h2620
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2621 | h2621
                        · rcases p2533_3 (m.d 0 3) (by simp) with h2622 | h2622
                          · linarith only [h2622, h4, hlam]
                          · linarith only [h2622, h8, hlam]
                        · linarith only [h2621, h6, hlam]
                      · linarith only [h2620, h3, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h1, hlam, p2533_1]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h4, hlam, p2533_1]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2630 | h2630
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2631 | h2631
                        · rcases p2533_3 (m.d 0 3) (by simp) with h2632 | h2632
                          · rcases p2533_3 (m.d 0 4) (by simp) with h2633 | h2633
                            · linarith only [h2633, h7, hlam]
                            · rcases p2533_3 (m.d 0 5) (by simp) with h2635 | h2635
                              · linarith only [h2635, h8, hlam]
                              · linarith only [h2635, h9, hlam]
                          · linarith only [h2632, h7, hlam]
                        · linarith only [h2631, h5, hlam]
                      · linarith only [h2, h2630, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2641 | h2641
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2642 | h2642
                        · rcases p2533_3 (m.d 0 3) (by simp) with h2643 | h2643
                          · rcases p2533_3 (m.d 0 4) (by simp) with h2644 | h2644
                            · linarith only [h2644, h7, hlam]
                            · rcases p2533_3 (m.d 0 5) (by simp) with h2646 | h2646
                              · linarith only [h2646, h8, hlam]
                              · rcases h2bigk with h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h0, h2520, h2527, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  rcases p2648_3 (m.d 0 2) (by simp) with h2651 | h2651
                                  · rcases p2648_3 (m.d 1 2) (by simp) with h2652 | h2652
                                    · linarith only [h0, h2652, hlam]
                                    · linarith only [h2520, h2652, hlam]
                                  · linarith only [h2651, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  rcases p2648_3 (m.d 0 2) (by simp) with h2656 | h2656
                                  · rcases p2648_3 (m.d 1 2) (by simp) with h2657 | h2657
                                    · linarith only [h0, h2657, hlam]
                                    · linarith only [h2521, h2657, hlam]
                                  · linarith only [h2656, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  rcases p2648_3 (m.d 0 2) (by simp) with h2661 | h2661
                                  · rcases p2648_3 (m.d 1 2) (by simp) with h2662 | h2662
                                    · linarith only [h0, h2662, hlam]
                                    · linarith only [h2522, h2662, hlam]
                                  · linarith only [h2661, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h0, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h0, h2528, h2531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  rcases p2648_3 (m.d 0 2) (by simp) with h2669 | h2669
                                  · rcases p2648_3 (m.d 1 2) (by simp) with h2670 | h2670
                                    · rcases p2648_3 (m.d 2 3) (by simp) with h2671 | h2671
                                      · linarith only [h2520, h2671, hlam]
                                      · linarith only [h2527, h2671, hlam]
                                    · linarith only [h2670, hlam, p2648_0]
                                  · linarith only [h2669, h5, hlam]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  rcases p2648_3 (m.d 0 2) (by simp) with h2676 | h2676
                                  · rcases p2648_3 (m.d 1 2) (by simp) with h2677 | h2677
                                    · rcases p2648_3 (m.d 2 3) (by simp) with h2678 | h2678
                                      · linarith only [h2520, h2678, hlam]
                                      · linarith only [h2528, h2678, hlam]
                                    · linarith only [h2677, hlam, p2648_0]
                                  · linarith only [h2676, h6, hlam]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h4, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h2520, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h0, h2520, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h0, h2520, hc01, hc25, hlam, hphi, ht0b, ht5b, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h5, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h2521, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h2527, hlam, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h2529, hlam, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h6, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h2522, hlam, p2648_0]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h2528, hlam, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [h0, h2527, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2533_1, p2648_1]
                                · have p2648_0 := h2648c.1
                                  have p2648_1 := h2648c.2.1
                                  have p2648_2 := h2648c.2.2.1
                                  have p2648_3 := h2648c.2.2.2
                                  linarith only [hlam, p2648_0]
                          · linarith only [h2643, h8, hlam]
                        · linarith only [h2642, h6, hlam]
                      · linarith only [h2641, h3, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h2, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h5, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h7, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h9, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h3, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h6, hlam, p2533_1]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [h8, hlam, p2533_0]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      rcases p2533_3 (m.d 0 1) (by simp) with h2709 | h2709
                      · rcases p2533_3 (m.d 0 2) (by simp) with h2710 | h2710
                        · rcases p2533_3 (m.d 0 3) (by simp) with h2711 | h2711
                          · rcases p2533_3 (m.d 0 4) (by simp) with h2712 | h2712
                            · linarith only [h2712, h9, hlam]
                            · rcases p2533_3 (m.d 0 5) (by simp) with h2714 | h2714
                              · rcases h2bigk with h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h0, h2520, h2527, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  rcases p2715_3 (m.d 0 2) (by simp) with h2718 | h2718
                                  · rcases p2715_3 (m.d 1 2) (by simp) with h2719 | h2719
                                    · linarith only [h0, h2719, hlam]
                                    · linarith only [h2520, h2719, hlam]
                                  · linarith only [h2718, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  rcases p2715_3 (m.d 0 2) (by simp) with h2723 | h2723
                                  · rcases p2715_3 (m.d 1 2) (by simp) with h2724 | h2724
                                    · linarith only [h0, h2724, hlam]
                                    · linarith only [h2521, h2724, hlam]
                                  · linarith only [h2723, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  rcases p2715_3 (m.d 0 2) (by simp) with h2728 | h2728
                                  · rcases p2715_3 (m.d 1 2) (by simp) with h2729 | h2729
                                    · linarith only [h0, h2729, hlam]
                                    · linarith only [h2522, h2729, hlam]
                                  · linarith only [h2728, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h0, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h0, h2528, h2531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  rcases p2715_3 (m.d 0 2) (by simp) with h2736 | h2736
                                  · rcases p2715_3 (m.d 1 2) (by simp) with h2737 | h2737
                                    · rcases p2715_3 (m.d 2 3) (by simp) with h2738 | h2738
                                      · linarith only [h2520, h2738, hlam]
                                      · linarith only [h2527, h2738, hlam]
                                    · linarith only [h2737, hlam, p2715_0]
                                  · linarith only [h2736, h5, hlam]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  rcases p2715_3 (m.d 0 2) (by simp) with h2743 | h2743
                                  · rcases p2715_3 (m.d 1 2) (by simp) with h2744 | h2744
                                    · rcases p2715_3 (m.d 2 3) (by simp) with h2745 | h2745
                                      · linarith only [h2520, h2745, hlam]
                                      · linarith only [h2528, h2745, hlam]
                                    · linarith only [h2744, hlam, p2715_0]
                                  · linarith only [h2743, h6, hlam]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h4, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h2520, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h0, h2520, h2527, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h0, h2520, hc01, hc25, hlam, hphi, ht0b, ht5b, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h5, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h2521, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h2527, hlam, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h2529, hlam, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h6, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h2522, hlam, p2715_0]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h2528, hlam, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [h0, h2522, h2527, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2715_1]
                                · have p2715_0 := h2715c.1
                                  have p2715_1 := h2715c.2.1
                                  have p2715_2 := h2715c.2.2.1
                                  have p2715_3 := h2715c.2.2.2
                                  linarith only [hlam, p2715_0]
                              · linarith only [h2714, h9, hlam]
                          · linarith only [h2711, h7, hlam]
                        · linarith only [h2710, h5, hlam]
                      · linarith only [h2, h2709, hlam]
                    · have p2533_0 := h2533c.1
                      have p2533_1 := h2533c.2.1
                      have p2533_2 := h2533c.2.2.1
                      have p2533_3 := h2533c.2.2.2
                      linarith only [hlam, p2533_0]
              · linarith only [h0, h2520, h2524, h2527, h2528, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2771 | h2771
              · linarith only [h0, h2520, h2523, h2527, h2771, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2773 | h2773
                · linarith only [h2, h2523, h2527, h2773, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2775 | h2775
                  · linarith only [h2, h2523, h2775, h9, hlam]
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
                      linarith only [h0, h2520, h2524, h2527, h2775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h1, h2524, h2527, h2775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      rcases p2777_3 (m.d 0 1) (by simp) with h2781 | h2781
                      · rcases p2777_3 (m.d 0 2) (by simp) with h2782 | h2782
                        · linarith only [h0, h2782, hlam]
                        · linarith only [h2782, h5, hlam]
                      · linarith only [h2, h2781, hlam]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      rcases p2777_3 (m.d 0 1) (by simp) with h2786 | h2786
                      · rcases p2777_3 (m.d 0 2) (by simp) with h2787 | h2787
                        · linarith only [h0, h2787, hlam]
                        · linarith only [h2787, h6, hlam]
                      · linarith only [h2786, h3, hlam]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h0, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h1, h2524, h2527, h2775, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      rcases p2777_3 (m.d 0 1) (by simp) with h2794 | h2794
                      · rcases p2777_3 (m.d 0 2) (by simp) with h2795 | h2795
                        · rcases p2777_3 (m.d 0 3) (by simp) with h2796 | h2796
                          · linarith only [h2796, h4, hlam]
                          · linarith only [h2796, h7, hlam]
                        · linarith only [h2795, h5, hlam]
                      · linarith only [h2, h2794, hlam]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      rcases p2777_3 (m.d 0 1) (by simp) with h2801 | h2801
                      · rcases p2777_3 (m.d 0 2) (by simp) with h2802 | h2802
                        · rcases p2777_3 (m.d 0 3) (by simp) with h2803 | h2803
                          · linarith only [h2803, h4, hlam]
                          · linarith only [h2803, h8, hlam]
                        · linarith only [h2802, h6, hlam]
                      · linarith only [h2801, h3, hlam]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h1, hlam, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h4, hlam, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      rcases p2777_3 (m.d 0 1) (by simp) with h2811 | h2811
                      · rcases p2777_3 (m.d 0 2) (by simp) with h2812 | h2812
                        · rcases p2777_3 (m.d 0 3) (by simp) with h2813 | h2813
                          · rcases p2777_3 (m.d 0 4) (by simp) with h2814 | h2814
                            · linarith only [h2814, h7, hlam]
                            · rcases p2777_3 (m.d 0 5) (by simp) with h2816 | h2816
                              · linarith only [h2816, h8, hlam]
                              · linarith only [h2816, h9, hlam]
                          · linarith only [h2813, h7, hlam]
                        · linarith only [h2812, h5, hlam]
                      · linarith only [h2, h2811, hlam]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      rcases p2777_3 (m.d 0 1) (by simp) with h2822 | h2822
                      · rcases p2777_3 (m.d 0 2) (by simp) with h2823 | h2823
                        · rcases p2777_3 (m.d 0 3) (by simp) with h2824 | h2824
                          · rcases p2777_3 (m.d 0 4) (by simp) with h2825 | h2825
                            · linarith only [h2825, h7, hlam]
                            · rcases p2777_3 (m.d 0 5) (by simp) with h2827 | h2827
                              · linarith only [h2827, h8, hlam]
                              · rcases h2bigk with h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h0, h2520, h2524, h2527, h2775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2829_1]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2527, h2775, h4, h8, hlam, p2777_1, p2829_2]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  rcases p2829_3 (m.d 0 2) (by simp) with h2833 | h2833
                                  · rcases p2829_3 (m.d 1 2) (by simp) with h2834 | h2834
                                    · linarith only [h0, h2834, hlam]
                                    · linarith only [h2521, h2834, hlam]
                                  · linarith only [h2833, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  rcases p2829_3 (m.d 0 2) (by simp) with h2838 | h2838
                                  · rcases p2829_3 (m.d 1 2) (by simp) with h2839 | h2839
                                    · linarith only [h0, h2839, hlam]
                                    · linarith only [h2522, h2839, hlam]
                                  · linarith only [h2838, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h0, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  rcases p2829_3 (m.d 0 2) (by simp) with h2845 | h2845
                                  · rcases p2829_3 (m.d 1 2) (by simp) with h2846 | h2846
                                    · rcases p2829_3 (m.d 2 3) (by simp) with h2847 | h2847
                                      · linarith only [h2847, hlam, p2829_0]
                                      · rcases p2829_3 (m.d 2 4) (by simp) with h2849 | h2849
                                        · linarith only [h2521, h2849, hlam]
                                        · linarith only [h2527, h2849, hlam]
                                    · linarith only [h2846, hlam, p2829_0]
                                  · linarith only [h2845, h4, hlam]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  rcases p2829_3 (m.d 0 2) (by simp) with h2854 | h2854
                                  · rcases p2829_3 (m.d 1 2) (by simp) with h2855 | h2855
                                    · rcases p2829_3 (m.d 2 3) (by simp) with h2856 | h2856
                                      · linarith only [h2520, h2856, hlam]
                                      · rcases p2829_3 (m.d 2 4) (by simp) with h2858 | h2858
                                        · linarith only [h2858, hlam, p2829_0]
                                        · rcases p2829_3 (m.d 2 5) (by simp) with h2860 | h2860
                                          · linarith only [h2522, h2860, hlam]
                                          · linarith only [h2773, h2860, hlam]
                                    · linarith only [h2855, hlam, p2829_0]
                                  · linarith only [h2854, h5, hlam]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  rcases p2829_3 (m.d 0 2) (by simp) with h2865 | h2865
                                  · rcases p2829_3 (m.d 1 2) (by simp) with h2866 | h2866
                                    · rcases p2829_3 (m.d 2 3) (by simp) with h2867 | h2867
                                      · linarith only [h2520, h2867, hlam]
                                      · rcases p2829_3 (m.d 2 4) (by simp) with h2869 | h2869
                                        · linarith only [h2521, h2869, hlam]
                                        · rcases p2829_3 (m.d 2 5) (by simp) with h2871 | h2871
                                          · linarith only [h2871, hlam, p2829_0]
                                          · rcases h3bigk with h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2524, h2527, h2775, h4, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              rcases p2873_3 (m.d 0 3) (by simp) with h2876 | h2876
                                              · rcases p2873_3 (m.d 1 3) (by simp) with h2877 | h2877
                                                · linarith only [h1, h2877, hlam]
                                                · linarith only [h2520, h2877, hlam]
                                              · linarith only [h2876, h4, hlam]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2527, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2527, h2775, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h1, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2520, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2520, h2527, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2520, h2527, h2775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h4, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2520, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2527, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2771, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h7, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2523, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [hc23, hc34, hlam, hphi, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2775, hlam, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h8, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h2524, hlam, p2873_0]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2524, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2777_1, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [h0, h2524, h3, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2777_1, p2873_1]
                                            · have p2873_0 := h2873c.1
                                              have p2873_1 := h2873c.2.1
                                              have p2873_2 := h2873c.2.2.1
                                              have p2873_3 := h2873c.2.2.2
                                              linarith only [hlam, p2873_0]
                                    · linarith only [h2866, hlam, p2829_0]
                                  · linarith only [h2865, h6, hlam]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h4, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2520, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2527, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2771, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h5, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2521, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h0, h4, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2777_1, p2829_1]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2773, hlam, p2829_1]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h6, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h2522, hlam, p2829_0]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2777_1, p2829_1]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [h0, h2524, h2771, h3, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2777_1, p2829_1]
                                · have p2829_0 := h2829c.1
                                  have p2829_1 := h2829c.2.1
                                  have p2829_2 := h2829c.2.2.1
                                  have p2829_3 := h2829c.2.2.2
                                  linarith only [hlam, p2829_0]
                          · linarith only [h2824, h8, hlam]
                        · linarith only [h2823, h6, hlam]
                      · linarith only [h2822, h3, hlam]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h2, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h5, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h7, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h9, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h3, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h6, hlam, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h8, hlam, p2777_0]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [h2, h2523, h2527, h9, hc23, hc45, hlam, hphi, ht34, p2777_1]
                    · have p2777_0 := h2777c.1
                      have p2777_1 := h2777c.2.1
                      have p2777_2 := h2777c.2.2.1
                      have p2777_3 := h2777c.2.2.2
                      linarith only [hlam, p2777_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2933 | h2933
          · linarith only [h2, h2523, h2524, h2933, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2935 | h2935
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2936 | h2936
              · linarith only [h2520, h2524, h2936, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2938 | h2938
                · linarith only [h2938, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2940 | h2940
                  · linarith only [h2520, h2524, h2935, h2940, h8, h9, hlam]
                  · rcases h0bigk with h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h2935, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h2520, h2524, h2935, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      rcases p2942_3 (m.d 0 1) (by simp) with h2946 | h2946
                      · rcases p2942_3 (m.d 0 2) (by simp) with h2947 | h2947
                        · linarith only [h0, h2947, hlam]
                        · linarith only [h2947, h5, hlam]
                      · linarith only [h2, h2946, hlam]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h2520, h2524, h2935, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h0, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h2520, h2524, h2935, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      rcases p2942_3 (m.d 0 1) (by simp) with h2955 | h2955
                      · rcases p2942_3 (m.d 0 2) (by simp) with h2956 | h2956
                        · rcases p2942_3 (m.d 0 3) (by simp) with h2957 | h2957
                          · linarith only [h2957, h4, hlam]
                          · linarith only [h2957, h7, hlam]
                        · linarith only [h2956, h5, hlam]
                      · linarith only [h2, h2955, hlam]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h0, h2520, h2524, h2935, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h1, hlam, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h4, hlam, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      rcases p2942_3 (m.d 0 1) (by simp) with h2966 | h2966
                      · rcases p2942_3 (m.d 0 2) (by simp) with h2967 | h2967
                        · rcases p2942_3 (m.d 0 3) (by simp) with h2968 | h2968
                          · rcases p2942_3 (m.d 0 4) (by simp) with h2969 | h2969
                            · linarith only [h2969, h7, hlam]
                            · rcases p2942_3 (m.d 0 5) (by simp) with h2971 | h2971
                              · linarith only [h2971, h8, hlam]
                              · linarith only [h2971, h9, hlam]
                          · linarith only [h2968, h7, hlam]
                        · linarith only [h2967, h5, hlam]
                      · linarith only [h2, h2966, hlam]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h2520, h2524, h2935, h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h2, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h5, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h7, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h9, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h3, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h6, hlam, p2942_1]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [h8, hlam, p2942_0]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      rcases p2942_3 (m.d 0 1) (by simp) with h2986 | h2986
                      · rcases p2942_3 (m.d 0 2) (by simp) with h2987 | h2987
                        · rcases p2942_3 (m.d 0 3) (by simp) with h2988 | h2988
                          · rcases p2942_3 (m.d 0 4) (by simp) with h2989 | h2989
                            · linarith only [h2989, h9, hlam]
                            · rcases p2942_3 (m.d 0 5) (by simp) with h2991 | h2991
                              · rcases h2bigk with h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h0, h2520, h2935, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  rcases p2992_3 (m.d 0 2) (by simp) with h2995 | h2995
                                  · rcases p2992_3 (m.d 1 2) (by simp) with h2996 | h2996
                                    · linarith only [h0, h2996, hlam]
                                    · linarith only [h2520, h2996, hlam]
                                  · linarith only [h2995, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  rcases p2992_3 (m.d 0 2) (by simp) with h3000 | h3000
                                  · rcases p2992_3 (m.d 1 2) (by simp) with h3001 | h3001
                                    · linarith only [h0, h3001, hlam]
                                    · linarith only [h2521, h3001, hlam]
                                  · linarith only [h3000, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  rcases p2992_3 (m.d 0 2) (by simp) with h3005 | h3005
                                  · rcases p2992_3 (m.d 1 2) (by simp) with h3006 | h3006
                                    · linarith only [h0, h3006, hlam]
                                    · linarith only [h2522, h3006, hlam]
                                  · linarith only [h3005, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h0, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h0, h2935, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  rcases p2992_3 (m.d 0 2) (by simp) with h3013 | h3013
                                  · rcases p2992_3 (m.d 1 2) (by simp) with h3014 | h3014
                                    · rcases p2992_3 (m.d 2 3) (by simp) with h3015 | h3015
                                      · linarith only [h2520, h3015, hlam]
                                      · linarith only [h2935, h3015, hlam]
                                    · linarith only [h3014, hlam, p2992_0]
                                  · linarith only [h3013, h5, hlam]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h0, h2935, h2936, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h4, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2520, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2520, h2524, h4, h8, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2936, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h5, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2521, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2935, hlam, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2938, hlam, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h6, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h2522, hlam, p2992_0]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h0, h2522, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [h0, h2522, h2935, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2992_1]
                                · have p2992_0 := h2992c.1
                                  have p2992_1 := h2992c.2.1
                                  have p2992_2 := h2992c.2.2.1
                                  have p2992_3 := h2992c.2.2.2
                                  linarith only [hlam, p2992_0]
                              · linarith only [h2991, h9, hlam]
                          · linarith only [h2988, h7, hlam]
                        · linarith only [h2987, h5, hlam]
                      · linarith only [h2, h2986, hlam]
                    · have p2942_0 := h2942c.1
                      have p2942_1 := h2942c.2.1
                      have p2942_2 := h2942c.2.2.1
                      have p2942_3 := h2942c.2.2.2
                      linarith only [hlam, p2942_0]
            · linarith only [h0, h2523, h2524, h2935, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3042 | h3042
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3043 | h3043
          · linarith only [h2523, h3042, h3043, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2523, h3042, h3043, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3046 | h3046
          · linarith only [h2, h2523, h3046, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3048 | h3048
            · linarith only [h2520, h2523, h3048, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3050 | h3050
              · linarith only [h2520, h3042, h3050, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3052 | h3052
                · linarith only [h0, h2520, h2523, h3052, h5, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3054 | h3054
                  · linarith only [h3054, h7, h9, hlam]
                  · rcases h0bigk with h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2520, h2523, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2520, h2523, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      rcases p3056_3 (m.d 0 1) (by simp) with h3060 | h3060
                      · rcases p3056_3 (m.d 0 2) (by simp) with h3061 | h3061
                        · linarith only [h0, h3061, hlam]
                        · linarith only [h3061, h5, hlam]
                      · linarith only [h2, h3060, hlam]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      rcases p3056_3 (m.d 0 1) (by simp) with h3065 | h3065
                      · rcases p3056_3 (m.d 0 2) (by simp) with h3066 | h3066
                        · linarith only [h0, h3066, hlam]
                        · linarith only [h3066, h6, hlam]
                      · linarith only [h3, h3065, hlam]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h0, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2520, h2523, h3054, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      rcases p3056_3 (m.d 0 1) (by simp) with h3073 | h3073
                      · rcases p3056_3 (m.d 0 2) (by simp) with h3074 | h3074
                        · rcases p3056_3 (m.d 0 3) (by simp) with h3075 | h3075
                          · linarith only [h3075, h4, hlam]
                          · linarith only [h3075, h7, hlam]
                        · linarith only [h3074, h5, hlam]
                      · linarith only [h2, h3073, hlam]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      rcases p3056_3 (m.d 0 1) (by simp) with h3080 | h3080
                      · rcases p3056_3 (m.d 0 2) (by simp) with h3081 | h3081
                        · rcases p3056_3 (m.d 0 3) (by simp) with h3082 | h3082
                          · linarith only [h3082, h4, hlam]
                          · linarith only [h3082, h8, hlam]
                        · linarith only [h3081, h6, hlam]
                      · linarith only [h3, h3080, hlam]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h1, hlam, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h4, hlam, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      rcases p3056_3 (m.d 0 1) (by simp) with h3090 | h3090
                      · rcases p3056_3 (m.d 0 2) (by simp) with h3091 | h3091
                        · rcases p3056_3 (m.d 0 3) (by simp) with h3092 | h3092
                          · rcases p3056_3 (m.d 0 4) (by simp) with h3093 | h3093
                            · linarith only [h3093, h7, hlam]
                            · rcases p3056_3 (m.d 0 5) (by simp) with h3095 | h3095
                              · linarith only [h3095, h8, hlam]
                              · linarith only [h3095, h9, hlam]
                          · linarith only [h3092, h7, hlam]
                        · linarith only [h3091, h5, hlam]
                      · linarith only [h2, h3090, hlam]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      rcases p3056_3 (m.d 0 1) (by simp) with h3101 | h3101
                      · rcases p3056_3 (m.d 0 2) (by simp) with h3102 | h3102
                        · rcases p3056_3 (m.d 0 3) (by simp) with h3103 | h3103
                          · rcases p3056_3 (m.d 0 4) (by simp) with h3104 | h3104
                            · linarith only [h3104, h7, hlam]
                            · rcases p3056_3 (m.d 0 5) (by simp) with h3106 | h3106
                              · linarith only [h3106, h8, hlam]
                              · rcases h2bigk with h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  rcases p3108_3 (m.d 0 2) (by simp) with h3110 | h3110
                                  · rcases p3108_3 (m.d 1 2) (by simp) with h3111 | h3111
                                    · linarith only [h0, h3111, hlam]
                                    · rcases p3108_3 (m.d 2 3) (by simp) with h3113 | h3113
                                      · linarith only [h3113, h4, hlam]
                                      · rcases p3108_3 (m.d 2 4) (by simp) with h3115 | h3115
                                        · linarith only [h3115, h5, hlam]
                                        · rcases p3108_3 (m.d 2 5) (by simp) with h3117 | h3117
                                          · linarith only [h3117, h6, hlam]
                                          · rcases h3bigk with h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              rcases p3119_3 (m.d 0 3) (by simp) with h3121 | h3121
                                              · rcases p3119_3 (m.d 1 3) (by simp) with h3122 | h3122
                                                · linarith only [h1, h3122, hlam]
                                                · rcases p3119_3 (m.d 2 3) (by simp) with h3124 | h3124
                                                  · linarith only [h3124, h4, hlam]
                                                  · rcases p3119_3 (m.d 3 4) (by simp) with h3126 | h3126
                                                    · linarith only [h3126, h7, hlam]
                                                    · linarith only [h2523, h3126, hlam]
                                              · linarith only [h1, h3121, hlam]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              rcases p3119_3 (m.d 0 3) (by simp) with h3130 | h3130
                                              · rcases p3119_3 (m.d 1 3) (by simp) with h3131 | h3131
                                                · linarith only [h1, h3131, hlam]
                                                · linarith only [h2520, h3131, hlam]
                                              · linarith only [h3130, h4, hlam]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h0, h2520, h2523, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h0, h2520, h2523, h3054, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h1, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h2523, h7, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h2523, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h3042, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h4, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h2520, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h3048, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h3050, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h7, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [hc13, hc34, hlam, hphi, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h0, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h3054, hlam, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h8, hlam, p3119_0]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1, p3119_1]
                                            · have p3119_0 := h3119c.1
                                              have p3119_1 := h3119c.2.1
                                              have p3119_2 := h3119c.2.2.1
                                              have p3119_3 := h3119c.2.2.2
                                              linarith only [hlam, p3119_0]
                                  · linarith only [h0, h3110, hlam]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h2520, h2523, h4, h7, h9, hlam, p3056_1, p3108_2]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  rcases p3108_3 (m.d 0 2) (by simp) with h3159 | h3159
                                  · rcases p3108_3 (m.d 1 2) (by simp) with h3160 | h3160
                                    · linarith only [h0, h3160, hlam]
                                    · linarith only [h2521, h3160, hlam]
                                  · linarith only [h3159, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  rcases p3108_3 (m.d 0 2) (by simp) with h3164 | h3164
                                  · rcases p3108_3 (m.d 1 2) (by simp) with h3165 | h3165
                                    · linarith only [h0, h3165, hlam]
                                    · linarith only [h2522, h3165, hlam]
                                  · linarith only [h3164, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h0, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  rcases p3108_3 (m.d 0 2) (by simp) with h3171 | h3171
                                  · rcases p3108_3 (m.d 1 2) (by simp) with h3172 | h3172
                                    · rcases p3108_3 (m.d 2 3) (by simp) with h3173 | h3173
                                      · linarith only [h3173, hlam, p3108_0]
                                      · rcases p3108_3 (m.d 2 4) (by simp) with h3175 | h3175
                                        · linarith only [h2521, h3175, hlam]
                                        · linarith only [h3048, h3175, hlam]
                                    · linarith only [h3172, hlam, p3108_0]
                                  · linarith only [h3171, h4, hlam]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  rcases p3108_3 (m.d 0 2) (by simp) with h3180 | h3180
                                  · rcases p3108_3 (m.d 1 2) (by simp) with h3181 | h3181
                                    · rcases p3108_3 (m.d 2 3) (by simp) with h3182 | h3182
                                      · linarith only [h2520, h3182, hlam]
                                      · rcases p3108_3 (m.d 2 4) (by simp) with h3184 | h3184
                                        · linarith only [h3184, hlam, p3108_0]
                                        · rcases p3108_3 (m.d 2 5) (by simp) with h3186 | h3186
                                          · linarith only [h2522, h3186, hlam]
                                          · linarith only [h3052, h3186, hlam]
                                    · linarith only [h3181, hlam, p3108_0]
                                  · linarith only [h3180, h5, hlam]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  rcases p3108_3 (m.d 0 2) (by simp) with h3191 | h3191
                                  · rcases p3108_3 (m.d 1 2) (by simp) with h3192 | h3192
                                    · rcases p3108_3 (m.d 2 3) (by simp) with h3193 | h3193
                                      · linarith only [h2520, h3193, hlam]
                                      · rcases p3108_3 (m.d 2 4) (by simp) with h3195 | h3195
                                        · linarith only [h2521, h3195, hlam]
                                        · rcases p3108_3 (m.d 2 5) (by simp) with h3197 | h3197
                                          · linarith only [h3197, hlam, p3108_0]
                                          · rcases h3bigk with h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              rcases p3199_3 (m.d 0 3) (by simp) with h3201 | h3201
                                              · rcases p3199_3 (m.d 1 3) (by simp) with h3202 | h3202
                                                · linarith only [h1, h3202, hlam]
                                                · rcases p3199_3 (m.d 2 3) (by simp) with h3204 | h3204
                                                  · linarith only [h3204, h4, hlam]
                                                  · rcases p3199_3 (m.d 3 4) (by simp) with h3206 | h3206
                                                    · linarith only [h3206, h7, hlam]
                                                    · linarith only [h2523, h3206, hlam]
                                              · linarith only [h1, h3201, hlam]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              rcases p3199_3 (m.d 0 3) (by simp) with h3210 | h3210
                                              · rcases p3199_3 (m.d 1 3) (by simp) with h3211 | h3211
                                                · linarith only [h1, h3211, hlam]
                                                · linarith only [h2520, h3211, hlam]
                                              · linarith only [h3210, h4, hlam]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h0, h2523, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h0, h2520, h3042, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h1, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h2523, hc23, hc34, hlam, hphi, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h2523, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h3042, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h4, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h2520, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h3048, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h3050, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h7, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [hc13, hc34, hlam, hphi, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h0, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h3054, hlam, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h8, hlam, p3199_0]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h2520, hc23, hc35, hlam, hphi, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1, p3199_1]
                                            · have p3199_0 := h3199c.1
                                              have p3199_1 := h3199c.2.1
                                              have p3199_2 := h3199c.2.2.1
                                              have p3199_3 := h3199c.2.2.2
                                              linarith only [hlam, p3199_0]
                                    · linarith only [h3192, hlam, p3108_0]
                                  · linarith only [h3191, h6, hlam]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h4, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h2520, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h3048, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h3050, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h5, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h2521, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h0, h2, h2521, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3108_1]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h3052, hlam, p3108_1]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h6, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h2522, hlam, p3108_0]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1, p3108_1]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [h0, h2522, h3042, h4, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3056_1, p3108_1]
                                · have p3108_0 := h3108c.1
                                  have p3108_1 := h3108c.2.1
                                  have p3108_2 := h3108c.2.2.1
                                  have p3108_3 := h3108c.2.2.2
                                  linarith only [hlam, p3108_0]
                          · linarith only [h3103, h8, hlam]
                        · linarith only [h3102, h6, hlam]
                      · linarith only [h3, h3101, hlam]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h5, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h7, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h9, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h6, hlam, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h8, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2520, h2523, h7, h9, hc23, hc45, hlam, hphi, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3267 | h3267
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3268 | h3268
        · linarith only [h2520, h2522, h3268, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3270 | h3270
          · linarith only [h2, h3270, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3272 | h3272
            · linarith only [h0, h2520, h2522, h3272, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h3267, h3268, h3272, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3275 | h3275
        · linarith only [h2520, h2522, h3267, h3275, h7, h9, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3277 | h3277
          · linarith only [h0, h2521, h3267, h3277, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3279 | h3279
            · linarith only [h0, h2520, h2522, h3267, h3279, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3281 | h3281
              · linarith only [h0, h2520, h2522, h3275, h3281, h6, hc01, hc15, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3283 | h3283
                · linarith only [h0, h2521, h2522, h3281, h3283, h4, h8, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3285 | h3285
                  · linarith only [h2521, h2522, h3281, h3285, h7, h8, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c | h3287c
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h2521, h2522, h3279, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h2521, h2522, h3279, h3281, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      rcases p3287_3 (m.d 0 1) (by simp) with h3291 | h3291
                      · rcases p3287_3 (m.d 0 2) (by simp) with h3292 | h3292
                        · linarith only [h0, h3292, hlam]
                        · linarith only [h3292, h5, hlam]
                      · linarith only [h2, h3291, hlam]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h2521, h2522, h3279, h3281, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h0, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h2521, h2522, h3279, h3281, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      rcases p3287_3 (m.d 0 1) (by simp) with h3300 | h3300
                      · rcases p3287_3 (m.d 0 2) (by simp) with h3301 | h3301
                        · rcases p3287_3 (m.d 0 3) (by simp) with h3302 | h3302
                          · linarith only [h3302, h4, hlam]
                          · linarith only [h3302, h7, hlam]
                        · linarith only [h3301, h5, hlam]
                      · linarith only [h2, h3300, hlam]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h0, h2521, h2522, h3279, h3281, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h1, hlam, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h4, hlam, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      rcases p3287_3 (m.d 0 1) (by simp) with h3311 | h3311
                      · rcases p3287_3 (m.d 0 2) (by simp) with h3312 | h3312
                        · rcases p3287_3 (m.d 0 3) (by simp) with h3313 | h3313
                          · rcases p3287_3 (m.d 0 4) (by simp) with h3314 | h3314
                            · linarith only [h3314, h7, hlam]
                            · rcases p3287_3 (m.d 0 5) (by simp) with h3316 | h3316
                              · linarith only [h3316, h8, hlam]
                              · linarith only [h3316, h9, hlam]
                          · linarith only [h3313, h7, hlam]
                        · linarith only [h3312, h5, hlam]
                      · linarith only [h2, h3311, hlam]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h0, h2521, h2522, h3279, h3281, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h2, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h5, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h7, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h9, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h3, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h6, hlam, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h8, hlam, p3287_0]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [h2520, h3267, h7, h9, hc23, hc45, hlam, hphi, ht34, p3287_1]
                    · have p3287_0 := h3287c.1
                      have p3287_1 := h3287c.2.1
                      have p3287_2 := h3287c.2.2.1
                      have p3287_3 := h3287c.2.2.2
                      linarith only [hlam, p3287_0]
  · linarith only [h2520, h2521, h5, h9, hc23, hc45, hlam, hphi, ht34]

end R2N4
