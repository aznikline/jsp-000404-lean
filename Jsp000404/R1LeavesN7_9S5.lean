import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5280000 in
set_option maxHeartbeats 5280000 in
theorem r1l7_13_24_L_I_H_I_s6 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_13_24_L_I_H_I_s7 m hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2542 | h2542
    · linarith only [h2542, h6, h7, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2544 | h2544
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2545 | h2545
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2546 | h2546
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2547 | h2547
            · linarith only [h1, h2547, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2549 | h2549
              · linarith only [h2, h2542, h2549, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2551 | h2551
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2552 | h2552
                  · linarith only [h1, h2544, h2552, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2554 | h2554
                    · linarith only [h2, h2542, h2545, h2554, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2556 | h2556
                      · linarith only [h2542, h2544, h2551, h2556, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h3bigk with h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2556, h7, hc13, hc45, hlam, hphi, ht34, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2556, h7, hc23, hc45, hlam, hphi, ht34, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2556, h7, hc34, hc45, hlam, hphi, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h7, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h1, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h1, h2556, h7, hc23, hc45, hlam, hphi, ht34, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h1, h2556, h7, hc34, hc45, hlam, hphi, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2547, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h4, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2544, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2556, h4, h7, hc34, hc45, hlam, hphi, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2552, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h6, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2546, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2551, hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [hlam, p2558_0]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2556, hlam, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2556, h6, hc34, hc45, hlam, hphi, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2546, h2556, hc34, hc45, hlam, hphi, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [h2551, h2556, hc34, hc45, hlam, hphi, p2558_1]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          rcases p2558_3 (m.d 0 3) (by simp) with h2582 | h2582
                          · linarith only [h2582, h7, hlam]
                          · linarith only [h2582, h6, hlam]
                        · have p2558_0 := h2558c.1
                          have p2558_1 := h2558c.2.1
                          have p2558_2 := h2558c.2.2.1
                          have p2558_3 := h2558c.2.2.2
                          linarith only [hlam, p2558_0]
                · linarith only [h2551, h6, h7, hc23, hc35, hlam, hphi]
          · linarith only [h2546, h6, h7, hc13, hc35, hlam, hphi]
        · linarith only [h2544, h2545, h5, h6, h7, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2589 | h2589
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2590 | h2590
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2591 | h2591
            · linarith only [h1, h2591, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2593 | h2593
              · linarith only [h2, h2542, h2593, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2595 | h2595
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2596 | h2596
                  · linarith only [h2596, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2598 | h2598
                    · linarith only [h2542, h2544, h2589, h2598, h4, h7, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2600 | h2600
                      · linarith only [h2542, h2544, h2589, h2595, h2600, h4, h7, hlam]
                      · linarith only [h2544, h2589, h2600, h4, h7, hc24, hc45, hlam, hphi]
                · linarith only [h2544, h2589, h2595, h6, h7, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h2590, h6, h7, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2605 | h2605
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2606 | h2606
            · linarith only [h1, h2606, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2608 | h2608
              · linarith only [h2, h2542, h2608, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2610 | h2610
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2611 | h2611
                  · linarith only [h2611, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2613 | h2613
                    · linarith only [h2542, h2613, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2615 | h2615
                      · linarith only [h2542, h2589, h2615, h5, hc12, hc34, hlam, hphi, ht23]
                      · rcases h3bigk with h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c | h2617c
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, h7, hc13, hc45, hlam, hphi, ht34, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, h7, hc23, hc45, hlam, hphi, ht34, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, h7, hc34, hc45, hlam, hphi, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h7, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h1, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2544, hlam, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h1, h2615, h7, hc34, hc45, hlam, hphi, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2606, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h4, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, h4, h7, hc13, hc45, hlam, hphi, ht34, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, h4, h7, hc34, hc45, hlam, hphi, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2611, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h6, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2605, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2610, hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [hlam, p2617_0]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, hlam, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2615, h6, hc34, hc45, hlam, hphi, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2605, h2615, hc34, hc45, hlam, hphi, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [h2544, h2615, hc12, hc45, hlam, hphi, ht23, ht34, p2617_1]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          rcases p2617_3 (m.d 0 3) (by simp) with h2641 | h2641
                          · linarith only [h2641, h7, hlam]
                          · linarith only [h2641, h6, hlam]
                        · have p2617_0 := h2617c.1
                          have p2617_1 := h2617c.2.1
                          have p2617_2 := h2617c.2.2.1
                          have p2617_3 := h2617c.2.2.2
                          linarith only [hlam, p2617_0]
                · linarith only [h1, h2605, h2610, h7, hc23, hc35, hlam, hphi]
          · linarith only [h2605, h6, h7, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 6906000 in
set_option maxHeartbeats 6906000 in
theorem r1l7_13_24_L_I_H_I_s5_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  exact r1l7_13_24_L_I_H_I_s6 m hb3 hb4 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 6906000 in
set_option maxHeartbeats 6906000 in
theorem r1l7_13_24_L_I_H_I_s5_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2647 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h2648 | h2648
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2649 | h2649
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2650 | h2650
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2651 | h2651
        · linarith only [h1, h2647, h2651, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2653 | h2653
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2654 | h2654
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2655 | h2655
              · linarith only [h2655, h4, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2657 | h2657
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2658 | h2658
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2659 | h2659
                    · rcases h3bigk with h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h6, hc13, hc34, hlam, hphi, p2660_1]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h6, hc23, hc34, hlam, hphi, p2660_1]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h6, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        rcases p2660_3 (m.d 0 3) (by simp) with h2665 | h2665
                        · rcases p2660_3 (m.d 1 3) (by simp) with h2666 | h2666
                          · linarith only [h1, h2666, hlam]
                          · linarith only [h2653, h2666, hlam]
                        · linarith only [h2665, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h1, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h1, h2657, h2659, hc01, hc45, hlam, hphi, ht0b, ht5b, p2660_1]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2651, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        rcases p2660_3 (m.d 0 3) (by simp) with h2674 | h2674
                        · rcases p2660_3 (m.d 1 3) (by simp) with h2675 | h2675
                          · rcases p2660_3 (m.d 2 3) (by simp) with h2676 | h2676
                            · linarith only [h2649, h2676, hlam]
                            · linarith only [h2657, h2676, hlam]
                          · linarith only [h2675, hlam, p2660_0]
                        · linarith only [h2647, h2674, hlam]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h4, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2649, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2655, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h0, h2649, h2659, hc01, hc45, hlam, hphi, ht0b, ht5b, p2660_1]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        rcases p2660_3 (m.d 0 3) (by simp) with h2686 | h2686
                        · linarith only [h2686, hlam, p2660_0]
                        · rcases p2660_3 (m.d 1 3) (by simp) with h2688 | h2688
                          · linarith only [h2651, h2688, hlam]
                          · rcases p2660_3 (m.d 2 3) (by simp) with h2690 | h2690
                            · linarith only [h2655, h2690, hlam]
                            · rcases p2660_3 (m.d 3 4) (by simp) with h2692 | h2692
                              · rcases p2660_3 (m.d 3 5) (by simp) with h2693 | h2693
                                · linarith only [h2659, h2693, hlam]
                                · rcases h4bigk with h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c | h2695c
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2651, h6, hc13, hc34, hlam, hphi, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2655, h6, hc23, hc34, hlam, hphi, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h6, hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    rcases p2695_3 (m.d 0 4) (by simp) with h2700 | h2700
                                    · rcases p2695_3 (m.d 1 4) (by simp) with h2701 | h2701
                                      · linarith only [h2, h2701, hlam]
                                      · linarith only [h2654, h2701, hlam]
                                    · linarith only [h2700, hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2, hlam, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2655, h2657, h2659, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2651, hlam, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h0, h2650, hc01, hc45, hlam, hphi, ht0b, ht5b, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h5, hlam, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2650, hlam, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2655, hlam, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h1, h2649, h2657, h2659, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2649, h2651, h2657, h2659, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2655, h2657, h2659, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2695_1]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    rcases p2695_3 (m.d 0 4) (by simp) with h2719 | h2719
                                    · linarith only [h2719, h6, hlam]
                                    · linarith only [h2648, h2719, hlam]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2648, hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2654, hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2658, hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [h2659, hlam, p2695_0]
                                  · have p2695_0 := h2695c.1
                                    have p2695_1 := h2695c.2.1
                                    have p2695_2 := h2695c.2.2.1
                                    have p2695_3 := h2695c.2.2.2
                                    linarith only [hlam, p2695_0]
                              · linarith only [h2692, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        rcases p2660_3 (m.d 0 3) (by simp) with h2728 | h2728
                        · linarith only [h2728, h6, hlam]
                        · linarith only [h1, h2728, hlam]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        rcases p2660_3 (m.d 0 3) (by simp) with h2731 | h2731
                        · linarith only [h2731, h6, hlam]
                        · linarith only [h2731, h4, hlam]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        rcases p2660_3 (m.d 0 3) (by simp) with h2735 | h2735
                        · linarith only [h2735, h6, hlam]
                        · linarith only [h2647, h2735, hlam]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2647, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2653, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2657, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [h2659, hlam, p2660_0]
                      · have p2660_0 := h2660c.1
                        have p2660_1 := h2660c.2.1
                        have p2660_2 := h2660c.2.2.1
                        have p2660_3 := h2660c.2.2.2
                        linarith only [hlam, p2660_0]
                    · linarith only [h1, h2648, h2649, h2657, h2659, h6, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2, h2654, h2655, h2657, h2658, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1, h2653, h2657, h6, hc23, hc34, hlam, hphi]
            · linarith only [h2651, h2653, h2654, hlam]
          · linarith only [h2647, h2653, h6, hc13, hc34, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2748 | h2748
        · linarith only [h1, h2647, h2748, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2750 | h2750
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2751 | h2751
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2752 | h2752
              · linarith only [h2752, h4, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2754 | h2754
                · linarith only [h0, h2649, h2650, h2754, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1, h2750, h2754, h6, hc23, hc34, hlam, hphi]
            · linarith only [h2647, h2648, h2649, h2650, h2751, h6, hc23, hc34, hlam, hphi]
          · linarith only [h2647, h2750, h6, hc13, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2759 | h2759
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2760 | h2760
        · linarith only [h2649, h2760, h4, h6, hlam]
        · linarith only [h2649, h2759, h2760, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2763 | h2763
        · linarith only [h1, h2649, h2763, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2765 | h2765
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2766 | h2766
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2767 | h2767
              · linarith only [h2767, h4, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2769 | h2769
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2770 | h2770
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2771 | h2771
                    · rcases h3bigk with h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h6, hc13, hc34, hlam, hphi, p2772_1]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2649, h6, hc12, hc34, hlam, hphi, ht23, p2772_1]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h6, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        rcases p2772_3 (m.d 0 3) (by simp) with h2777 | h2777
                        · rcases p2772_3 (m.d 1 3) (by simp) with h2778 | h2778
                          · linarith only [h1, h2778, hlam]
                          · linarith only [h2765, h2778, hlam]
                        · linarith only [h2777, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h1, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2649, hlam, p2772_1]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2763, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        rcases p2772_3 (m.d 0 3) (by simp) with h2786 | h2786
                        · rcases p2772_3 (m.d 1 3) (by simp) with h2787 | h2787
                          · rcases p2772_3 (m.d 2 3) (by simp) with h2788 | h2788
                            · rcases p2772_3 (m.d 3 4) (by simp) with h2789 | h2789
                              · rcases p2772_3 (m.d 3 5) (by simp) with h2790 | h2790
                                · linarith only [h2790, hlam, p2772_0]
                                · rcases h4bigk with h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2763, h2771, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2772_1, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2649, h2767, h2771, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2772_1, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h6, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    rcases p2792_3 (m.d 0 4) (by simp) with h2797 | h2797
                                    · rcases p2792_3 (m.d 1 4) (by simp) with h2798 | h2798
                                      · linarith only [h2, h2798, hlam]
                                      · linarith only [h2766, h2798, hlam]
                                    · linarith only [h2797, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2, hlam, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2759, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2763, hlam, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h5, hlam, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2767, hlam, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2, h2763, h2771, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2772_1, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2763, h2771, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2772_1, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2759, hc12, hc34, hlam, hphi, ht23, p2792_1]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    rcases p2792_3 (m.d 0 4) (by simp) with h2816 | h2816
                                    · linarith only [h2816, h6, hlam]
                                    · linarith only [h2648, h2816, hlam]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2648, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2766, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2770, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [h2771, hlam, p2792_0]
                                  · have p2792_0 := h2792c.1
                                    have p2792_1 := h2792c.2.1
                                    have p2792_2 := h2792c.2.2.1
                                    have p2792_3 := h2792c.2.2.2
                                    linarith only [hlam, p2792_0]
                              · linarith only [h2771, h2789, hlam]
                            · linarith only [h2769, h2788, hlam]
                          · linarith only [h2787, hlam, p2772_0]
                        · linarith only [h2647, h2786, hlam]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h4, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h4, h6, hc13, hc34, hlam, hphi, p2772_1]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2767, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        rcases p2772_3 (m.d 0 3) (by simp) with h2832 | h2832
                        · rcases p2772_3 (m.d 1 3) (by simp) with h2833 | h2833
                          · linarith only [h2649, h2833, hlam]
                          · linarith only [h2765, h2833, hlam]
                        · linarith only [h2647, h2832, hlam]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2649, h4, hc12, hc34, hlam, hphi, ht23, p2772_1]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        rcases p2772_3 (m.d 0 3) (by simp) with h2838 | h2838
                        · linarith only [h2838, h6, hlam]
                        · linarith only [h1, h2838, hlam]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2649, hc12, hc34, hlam, hphi, ht23, p2772_1]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        rcases p2772_3 (m.d 0 3) (by simp) with h2843 | h2843
                        · linarith only [h2843, h6, hlam]
                        · linarith only [h2647, h2843, hlam]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2647, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2765, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2769, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [h2771, hlam, p2772_0]
                      · have p2772_0 := h2772c.1
                        have p2772_1 := h2772c.2.1
                        have p2772_2 := h2772c.2.2.1
                        have p2772_3 := h2772c.2.2.2
                        linarith only [hlam, p2772_0]
                    · linarith only [h2649, h2771, h4, h6, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2, h2649, h2766, h2767, h2770, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1, h2649, h2765, h2769, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h2763, h2765, h2766, hlam]
          · linarith only [h2647, h2765, h6, hc13, hc34, hlam, hphi]
  · linarith only [h2647, h2648, h6, hlam]

end R2N4
