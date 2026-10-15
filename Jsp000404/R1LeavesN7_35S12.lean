import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2135 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2136 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2137 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2608 | h2608
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2609 | h2609
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2610 | h2610
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2611 | h2611
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2612 | h2612
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2613 | h2613
            · linarith only [h2134, h2137, h2613, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2615 | h2615
              · linarith only [h2134, h2137, h2609, h2612, h2615, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2617 | h2617
                · rcases h2bigk with h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h0, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    rcases p2618_3 (m.d 0 2) (by simp) with h2621 | h2621
                    · rcases p2618_3 (m.d 1 2) (by simp) with h2622 | h2622
                      · rcases p2618_3 (m.d 2 3) (by simp) with h2623 | h2623
                        · linarith only [h2623, hlam, p2618_0]
                        · rcases p2618_3 (m.d 2 4) (by simp) with h2625 | h2625
                          · linarith only [h2135, h2625, hlam]
                          · linarith only [h2613, h2625, hlam]
                      · linarith only [h2609, h2622, hlam]
                    · linarith only [h2621, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h0, h2617, hc12, hlam, hphi, ht01, ht0b, ht5b, p2618_1, u5ehi4]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2618_1, u5ehi2]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2618_1]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    rcases p2618_3 (m.d 0 2) (by simp) with h2634 | h2634
                    · linarith only [h0, h2634, hlam]
                    · linarith only [h2134, h2634, hlam]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2617, hc12, hlam, hphi, ht01, ht0b, ht5b, p2618_1, u5ehi4]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2617, hc12, hlam, hphi, ht01, ht0b, ht5b, p2618_1, u5ehi4]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2134, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2609, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2613, hlam, p2618_1]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2615, hlam, p2618_1]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2135, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2610, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2618_1]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2135, h2137, h2609, h2612, h2617, hc12, hlam, hphi, ht01, ht0b, ht5b, p2618_1, u5ehi4]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2136, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2611, hlam, p2618_0]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2618_1]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [h2617, hlam, p2618_1]
                  · have p2618_0 := h2618c.1
                    have p2618_1 := h2618c.2.1
                    have p2618_2 := h2618c.2.2.1
                    have p2618_3 := h2618c.2.2.2
                    linarith only [hlam, p2618_0]
                · rcases h2bigk with h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h0, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    rcases p2654_3 (m.d 0 2) (by simp) with h2657 | h2657
                    · rcases p2654_3 (m.d 1 2) (by simp) with h2658 | h2658
                      · rcases p2654_3 (m.d 2 3) (by simp) with h2659 | h2659
                        · linarith only [h2659, hlam, p2654_0]
                        · rcases p2654_3 (m.d 2 4) (by simp) with h2661 | h2661
                          · linarith only [h2135, h2661, hlam]
                          · linarith only [h2613, h2661, hlam]
                      · linarith only [h2609, h2658, hlam]
                    · linarith only [h2657, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    rcases p2654_3 (m.d 0 2) (by simp) with h2666 | h2666
                    · rcases p2654_3 (m.d 1 2) (by simp) with h2667 | h2667
                      · rcases p2654_3 (m.d 2 3) (by simp) with h2668 | h2668
                        · linarith only [h2134, h2668, hlam]
                        · rcases p2654_3 (m.d 2 4) (by simp) with h2670 | h2670
                          · linarith only [h2670, hlam, p2654_0]
                          · rcases p2654_3 (m.d 2 5) (by simp) with h2672 | h2672
                            · linarith only [h2136, h2672, hlam]
                            · linarith only [h2617, h2672, hlam]
                      · linarith only [h2610, h2667, hlam]
                    · linarith only [h2666, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2654_1, u5ehi2]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2654_1]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    rcases p2654_3 (m.d 0 2) (by simp) with h2680 | h2680
                    · linarith only [h0, h2680, hlam]
                    · linarith only [h2134, h2680, hlam]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    rcases p2654_3 (m.d 0 2) (by simp) with h2683 | h2683
                    · linarith only [h0, h2683, hlam]
                    · linarith only [h2135, h2683, hlam]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2654_1, u5ehi2]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2134, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2609, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2613, hlam, p2654_1]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2615, hlam, p2654_1]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2135, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2610, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2135, h2608, h2617, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2654_1]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2617, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2136, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2611, hlam, p2654_0]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [h2137, h2608, h2609, h2612, h2617, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2654_1]
                  · have p2654_0 := h2654c.1
                    have p2654_1 := h2654c.2.1
                    have p2654_2 := h2654c.2.2.1
                    have p2654_3 := h2654c.2.2.2
                    linarith only [hlam, p2654_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2702 | h2702
            · linarith only [h0, h2134, h2137, h2608, h2702, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2704 | h2704
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2705 | h2705
                · rcases h2bigk with h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h0, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h0, h2704, hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi3]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h0, h2702, h2704, hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi3]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi2]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2706_1]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2704, hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi3]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2702, h2704, hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi3]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi2]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2134, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2609, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2702, hlam, p2706_1]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2135, h2702, hc02, hlam, hphi, ht0b, ht5b, p2706_1, u5ehi2]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2135, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2610, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2706_1]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h0, h2135, h2704, hc12, hlam, hphi, ht01, ht0b, ht5b, p2706_1, u5ehi3]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2136, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2611, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2704, hlam, p2706_0]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [h2705, hlam, p2706_1]
                  · have p2706_0 := h2706c.1
                    have p2706_1 := h2706c.2.1
                    have p2706_2 := h2706c.2.2.1
                    have p2706_3 := h2706c.2.2.2
                    linarith only [hlam, p2706_0]
                · linarith only [h2137, h2608, h2702, h2704, h2705, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2733 | h2733
                · rcases h2bigk with h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c | h2734c
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h0, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    rcases p2734_3 (m.d 0 2) (by simp) with h2737 | h2737
                    · rcases p2734_3 (m.d 1 2) (by simp) with h2738 | h2738
                      · rcases p2734_3 (m.d 2 3) (by simp) with h2739 | h2739
                        · linarith only [h2739, hlam, p2734_0]
                        · rcases p2734_3 (m.d 2 4) (by simp) with h2741 | h2741
                          · linarith only [h2135, h2741, hlam]
                          · linarith only [h2702, h2741, hlam]
                      · linarith only [h2609, h2738, hlam]
                    · linarith only [h2737, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h0, h2733, hc12, hlam, hphi, ht01, ht0b, ht5b, p2734_1, u5ehi4]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2734_1, u5ehi2]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2734_1]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    rcases p2734_3 (m.d 0 2) (by simp) with h2750 | h2750
                    · linarith only [h0, h2750, hlam]
                    · linarith only [h2134, h2750, hlam]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2733, hc12, hlam, hphi, ht01, ht0b, ht5b, p2734_1, u5ehi4]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2733, hc12, hlam, hphi, ht01, ht0b, ht5b, p2734_1, u5ehi4]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2134, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2609, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2702, hlam, p2734_1]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2704, hlam, p2734_1]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2135, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2610, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2734_1]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h0, h2135, h2733, hc12, hlam, hphi, ht01, ht0b, ht5b, p2734_1, u5ehi4]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2136, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2611, hlam, p2734_0]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2734_1]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [h2733, hlam, p2734_1]
                  · have p2734_0 := h2734c.1
                    have p2734_1 := h2734c.2.1
                    have p2734_2 := h2734c.2.2.1
                    have p2734_3 := h2734c.2.2.2
                    linarith only [hlam, p2734_0]
                · rcases h2bigk with h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c | h2770c
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h0, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    rcases p2770_3 (m.d 0 2) (by simp) with h2773 | h2773
                    · rcases p2770_3 (m.d 1 2) (by simp) with h2774 | h2774
                      · rcases p2770_3 (m.d 2 3) (by simp) with h2775 | h2775
                        · linarith only [h2775, hlam, p2770_0]
                        · rcases p2770_3 (m.d 2 4) (by simp) with h2777 | h2777
                          · linarith only [h2135, h2777, hlam]
                          · linarith only [h2702, h2777, hlam]
                      · linarith only [h2609, h2774, hlam]
                    · linarith only [h2773, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    rcases p2770_3 (m.d 0 2) (by simp) with h2782 | h2782
                    · rcases p2770_3 (m.d 1 2) (by simp) with h2783 | h2783
                      · rcases p2770_3 (m.d 2 3) (by simp) with h2784 | h2784
                        · linarith only [h2134, h2784, hlam]
                        · rcases p2770_3 (m.d 2 4) (by simp) with h2786 | h2786
                          · linarith only [h2786, hlam, p2770_0]
                          · rcases p2770_3 (m.d 2 5) (by simp) with h2788 | h2788
                            · linarith only [h2136, h2788, hlam]
                            · linarith only [h2733, h2788, hlam]
                      · linarith only [h2610, h2783, hlam]
                    · linarith only [h2782, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2770_1, u5ehi2]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2770_1]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    rcases p2770_3 (m.d 0 2) (by simp) with h2796 | h2796
                    · linarith only [h0, h2796, hlam]
                    · linarith only [h2134, h2796, hlam]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    rcases p2770_3 (m.d 0 2) (by simp) with h2799 | h2799
                    · linarith only [h0, h2799, hlam]
                    · linarith only [h2135, h2799, hlam]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2770_1, u5ehi2]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2134, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2609, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2702, hlam, p2770_1]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2704, hlam, p2770_1]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2135, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2610, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2770_1]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2733, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2136, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2611, hlam, p2770_0]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2770_1]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [h2137, h2608, h2733, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2770_1]
                  · have p2770_0 := h2770c.1
                    have p2770_1 := h2770c.2.1
                    have p2770_2 := h2770c.2.2.1
                    have p2770_3 := h2770c.2.2.2
                    linarith only [hlam, p2770_0]
        · linarith only [h0, h2136, h2611, hlam]
      · linarith only [h0, h2135, h2610, hlam]
    · linarith only [h0, h2134, h2609, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2821 | h2821
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2822 | h2822
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2823 | h2823
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2824 | h2824
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2825 | h2825
            · linarith only [h2134, h2137, h2825, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2827 | h2827
              · linarith only [h2134, h2137, h2821, h2824, h2827, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2829 | h2829
                · linarith only [h2135, h2608, h2829, hlam]
                · rcases h2bigk with h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h0, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    rcases p2831_3 (m.d 0 2) (by simp) with h2834 | h2834
                    · rcases p2831_3 (m.d 1 2) (by simp) with h2835 | h2835
                      · rcases p2831_3 (m.d 2 3) (by simp) with h2836 | h2836
                        · linarith only [h2836, hlam, p2831_0]
                        · rcases p2831_3 (m.d 2 4) (by simp) with h2838 | h2838
                          · linarith only [h2135, h2838, hlam]
                          · linarith only [h2825, h2838, hlam]
                      · linarith only [h2821, h2835, hlam]
                    · linarith only [h2834, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    rcases p2831_3 (m.d 0 2) (by simp) with h2843 | h2843
                    · rcases p2831_3 (m.d 1 2) (by simp) with h2844 | h2844
                      · rcases p2831_3 (m.d 2 3) (by simp) with h2845 | h2845
                        · linarith only [h2134, h2845, hlam]
                        · rcases p2831_3 (m.d 2 4) (by simp) with h2847 | h2847
                          · linarith only [h2847, hlam, p2831_0]
                          · rcases p2831_3 (m.d 2 5) (by simp) with h2849 | h2849
                            · linarith only [h2136, h2849, hlam]
                            · linarith only [h2829, h2849, hlam]
                      · linarith only [h2822, h2844, hlam]
                    · linarith only [h2843, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2831_1, u5ehi2]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2831_1]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    rcases p2831_3 (m.d 0 2) (by simp) with h2857 | h2857
                    · linarith only [h0, h2857, hlam]
                    · linarith only [h2134, h2857, hlam]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    rcases p2831_3 (m.d 0 2) (by simp) with h2860 | h2860
                    · linarith only [h0, h2860, hlam]
                    · linarith only [h2135, h2860, hlam]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2831_1, u5ehi2]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2134, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2821, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2825, hlam, p2831_1]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2827, hlam, p2831_1]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2135, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2822, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2831_1]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2829, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2136, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h2823, hlam, p2831_0]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2831_1]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [h0, h2136, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2831_1]
                  · have p2831_0 := h2831c.1
                    have p2831_1 := h2831c.2.1
                    have p2831_2 := h2831c.2.2.1
                    have p2831_3 := h2831c.2.2.2
                    linarith only [hlam, p2831_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2879 | h2879
            · linarith only [h2134, h2137, h2879, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2881 | h2881
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2882 | h2882
                · linarith only [h2135, h2608, h2882, hlam]
                · linarith only [h2879, h2881, h2882, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2885 | h2885
                · linarith only [h2135, h2608, h2885, hlam]
                · rcases h2bigk with h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h0, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    rcases p2887_3 (m.d 0 2) (by simp) with h2890 | h2890
                    · rcases p2887_3 (m.d 1 2) (by simp) with h2891 | h2891
                      · rcases p2887_3 (m.d 2 3) (by simp) with h2892 | h2892
                        · linarith only [h2892, hlam, p2887_0]
                        · rcases p2887_3 (m.d 2 4) (by simp) with h2894 | h2894
                          · linarith only [h2135, h2894, hlam]
                          · linarith only [h2879, h2894, hlam]
                      · linarith only [h2821, h2891, hlam]
                    · linarith only [h2890, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    rcases p2887_3 (m.d 0 2) (by simp) with h2899 | h2899
                    · rcases p2887_3 (m.d 1 2) (by simp) with h2900 | h2900
                      · rcases p2887_3 (m.d 2 3) (by simp) with h2901 | h2901
                        · linarith only [h2134, h2901, hlam]
                        · rcases p2887_3 (m.d 2 4) (by simp) with h2903 | h2903
                          · linarith only [h2903, hlam, p2887_0]
                          · rcases p2887_3 (m.d 2 5) (by simp) with h2905 | h2905
                            · linarith only [h2136, h2905, hlam]
                            · linarith only [h2885, h2905, hlam]
                      · linarith only [h2822, h2900, hlam]
                    · linarith only [h2899, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2887_1, u5ehi2]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2887_1]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    rcases p2887_3 (m.d 0 2) (by simp) with h2913 | h2913
                    · linarith only [h0, h2913, hlam]
                    · linarith only [h2134, h2913, hlam]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    rcases p2887_3 (m.d 0 2) (by simp) with h2916 | h2916
                    · linarith only [h0, h2916, hlam]
                    · linarith only [h2135, h2916, hlam]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2887_1, u5ehi2]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2134, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2821, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2879, hlam, p2887_1]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2881, hlam, p2887_1]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2135, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2822, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2887_1]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2885, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2136, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h2823, hlam, p2887_0]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2887_1]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [h0, h2136, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2887_1]
                  · have p2887_0 := h2887c.1
                    have p2887_1 := h2887c.2.1
                    have p2887_2 := h2887c.2.2.1
                    have p2887_3 := h2887c.2.2.2
                    linarith only [hlam, p2887_0]
        · linarith only [h0, h2136, h2823, hlam]
      · linarith only [h0, h2135, h2822, hlam]
    · linarith only [h0, h2134, h2821, hlam]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2135 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2136 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2137 | h2137
  · exact r1l7_22_15_H_I_L_R_x1_x0_x0_x0_x0 m hb2 hb5 h0 h2134 h2135 h2136 h2137
  · exact r1l7_22_15_H_I_L_R_x1_x0_x0_x0_x1 m hb2 hb5 h0 h2134 h2135 h2136 h2137

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2135 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2136 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2938 | h2938
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2939 | h2939
    · linarith only [h2134, h2136, h2938, h2939, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2941 | h2941
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2942 | h2942
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2943 | h2943
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2944 | h2944
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2945 | h2945
              · linarith only [h2134, h2136, h2943, h2945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h2134, h2136, h2938, h2943, h2945, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h2134, h2136, h2938, h2943, h2944, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2949 | h2949
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2950 | h2950
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2951 | h2951
                · linarith only [h0, h2134, h2943, h2951, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2953 | h2953
                  · linarith only [h0, h2135, h2943, h2951, h2953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h0, h2134, h2943, h2950, h2953, hc34, hc45, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2956 | h2956
                · linarith only [h2134, h2938, h2950, h2956, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h0, h2134, h2938, h2943, h2950, h2956, hc23, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2959 | h2959
              · linarith only [h2941, h2949, h2959, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2961 | h2961
                · linarith only [h2134, h2938, h2941, h2949, h2961, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h0, h2134, h2938, h2943, h2949, h2961, hc13, hc35, hlam, hphi]
        · linarith only [h0, h2135, h2942, hlam]
      · linarith only [h0, h2134, h2941, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2966 | h2966
    · linarith only [h2135, h2136, h2966, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2968 | h2968
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2969 | h2969
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2970 | h2970
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2971 | h2971
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2972 | h2972
              · linarith only [h2134, h2136, h2938, h2970, h2972, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2974 | h2974
                · linarith only [h2134, h2938, h2971, h2974, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2976 | h2976
                  · linarith only [h2135, h2136, h2970, h2976, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases h2bigk with h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h0, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2136, h2970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2136, h2970, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2136, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      rcases p2978_3 (m.d 0 2) (by simp) with h2986 | h2986
                      · linarith only [h0, h2986, hlam]
                      · linarith only [h2134, h2986, hlam]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      rcases p2978_3 (m.d 0 2) (by simp) with h2989 | h2989
                      · linarith only [h0, h2989, hlam]
                      · linarith only [h2135, h2989, hlam]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2978_1, u5ehi2]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2134, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2968, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2972, hlam, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2974, hlam, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2135, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2969, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2976, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hc02, hc25, hlam, hphi, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2970, hlam, p2978_0]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [h2970, h2972, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2978_1]
                    · have p2978_0 := h2978c.1
                      have p2978_1 := h2978c.2.1
                      have p2978_2 := h2978c.2.2.1
                      have p2978_3 := h2978c.2.2.2
                      linarith only [hlam, p2978_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3008 | h3008
              · linarith only [h2134, h2136, h2970, h2971, h3008, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3010 | h3010
                · linarith only [h2134, h2136, h2970, h3010, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3012 | h3012
                  · linarith only [h2135, h2136, h2970, h3012, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases h2bigk with h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2136, h2970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2136, h2970, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2136, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      rcases p3014_3 (m.d 0 2) (by simp) with h3022 | h3022
                      · linarith only [h0, h3022, hlam]
                      · linarith only [h2134, h3022, hlam]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      rcases p3014_3 (m.d 0 2) (by simp) with h3025 | h3025
                      · linarith only [h0, h3025, hlam]
                      · linarith only [h2135, h3025, hlam]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2136, hc12, hlam, hphi, ht01, ht0b, ht5b, p3014_1, u5ehi0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2134, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2968, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h3008, hlam, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h3010, hlam, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2135, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2969, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h3012, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hc02, hc25, hlam, hphi, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2970, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2970, h3008, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3044 | h3044
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3045 | h3045
              · linarith only [h0, h2134, h2938, h2970, h3045, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3047 | h3047
                · linarith only [h0, h2134, h2970, h3047, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h2938, h2968, h2970, h3044, h3047, hc03, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3050 | h3050
              · linarith only [h0, h2134, h2970, h3044, h3050, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3052 | h3052
                · linarith only [h0, h2134, h2970, h3052, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3054 | h3054
                  · linarith only [h0, h2135, h2966, h2970, h3052, h3054, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases h2bigk with h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h0, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h0, h2970, h3054, hc23, hc45, hlam, hphi, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h0, h2970, h3054, hc24, hc45, hlam, hphi, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2136, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2970, h3054, hc02, hc45, hlam, hphi, ht23, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2970, h3054, hc23, hc45, hlam, hphi, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2970, h3054, hc24, hc45, hlam, hphi, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2970, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2134, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2968, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3050, hlam, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3052, hlam, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2135, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2969, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3054, hlam, p3056_0]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3054, hc02, hc45, hlam, hphi, ht23, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3054, hc12, hc45, hlam, hphi, ht23, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3054, hc23, hc45, hlam, hphi, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [h3050, h3054, hc23, hc45, hlam, hphi, ht34, p3056_1]
                    · have p3056_0 := h3056c.1
                      have p3056_1 := h3056c.2.1
                      have p3056_2 := h3056c.2.2.1
                      have p3056_3 := h3056c.2.2.2
                      linarith only [hlam, p3056_0]
        · linarith only [h0, h2135, h2969, hlam]
      · linarith only [h0, h2134, h2938, h2968, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2135 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2136 | h2136
  · exact r1l7_22_15_H_I_L_R_x1_x0_x0_x0 m hb2 hb5 h0 h2134 h2135 h2136
  · exact r1l7_22_15_H_I_L_R_x1_x0_x0_x1 m hb2 hb5 h0 h2134 h2135 h2136

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2135 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3084 | h3084
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3085 | h3085
    · linarith only [h2134, h2135, h3085, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3087 | h3087
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3088 | h3088
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3089 | h3089
          · linarith only [h2135, h3084, h3089, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3091 | h3091
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3092 | h3092
              · linarith only [h2135, h3084, h3085, h3088, h3089, h3092, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3094 | h3094
                · linarith only [h0, h2134, h3089, h3092, h3094, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3096 | h3096
                  · linarith only [h0, h2134, h3089, h3094, h3096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3098 | h3098
                    · rcases h2bigk with h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h0, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h0, h3089, h3094, hc23, hc34, hlam, hphi, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h2135, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h0, h3089, h3094, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3099_1, u5ehi2]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3089, h3094, hc02, hc34, hlam, hphi, ht23, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3089, h3094, hc23, hc34, hlam, hphi, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3089, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3089, h3094, h3098, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3099_1, u5ehi4]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h2134, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3088, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3094, hlam, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3096, hlam, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3084, h3094, h3098, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3099_1, u5ehi4]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3094, hc12, hc34, hlam, hphi, ht23, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3094, hc23, hc34, hlam, hphi, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3094, h3098, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3099_1, u5ehi4]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3084, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3091, hlam, p3099_0]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3084, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [h3098, hlam, p3099_1]
                      · have p3099_0 := h3099c.1
                        have p3099_1 := h3099c.2.1
                        have p3099_2 := h3099c.2.2.1
                        have p3099_3 := h3099c.2.2.2
                        linarith only [hlam, p3099_0]
                    · linarith only [h0, h3084, h3087, h3089, h3098, hc05, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h3084, h3091, hlam]
        · linarith only [h0, h2134, h3088, hlam]
      · linarith only [h2135, h3084, h3087, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3129 | h3129
    · linarith only [h2134, h2135, h3129, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3131 | h3131
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3132 | h3132
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3133 | h3133
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3134 | h3134
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3135 | h3135
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3136 | h3136
                · linarith only [h2134, h2135, h3129, h3133, h3136, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3138 | h3138
                  · linarith only [h2134, h2135, h3132, h3135, h3136, h3138, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3140 | h3140
                    · rcases h2bigk with h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h0, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3084, h3132, h3135, h3136, h3140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h2135, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3084, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        rcases p3141_3 (m.d 0 2) (by simp) with h3149 | h3149
                        · linarith only [h0, h3149, hlam]
                        · linarith only [h2134, h3149, hlam]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3140, hc12, hlam, hphi, ht01, ht0b, ht5b, p3141_1, u5ehi2]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h2134, h3084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h2134, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3132, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3136, hlam, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3138, hlam, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h2134, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3133, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3132, h3135, h3136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h2134, h3084, h3132, h3135, h3136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h2134, h3134, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3134, hlam, p3141_0]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3134, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [h3140, hlam, p3141_1]
                      · have p3141_0 := h3141c.1
                        have p3141_1 := h3141c.2.1
                        have p3141_2 := h3141c.2.2.1
                        have p3141_3 := h3141c.2.2.2
                        linarith only [hlam, p3141_0]
                    · linarith only [h2134, h2135, h3131, h3140, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3170 | h3170
                · linarith only [h2134, h2135, h3133, h3135, h3170, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3172 | h3172
                  · linarith only [h2134, h2135, h3133, h3172, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3174 | h3174
                    · rcases h2bigk with h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h0, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3084, h3133, h3174, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h2135, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3084, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        rcases p3175_3 (m.d 0 2) (by simp) with h3183 | h3183
                        · linarith only [h0, h3183, hlam]
                        · linarith only [h2134, h3183, hlam]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3174, hc12, hlam, hphi, ht01, ht0b, ht5b, p3175_1, u5ehi2]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h2134, h3084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h2134, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3132, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3170, hlam, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3172, hlam, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h2134, h3133, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3133, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h2134, h3084, h3133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h2134, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3134, hlam, p3175_0]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3134, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [h3174, hlam, p3175_1]
                      · have p3175_0 := h3175c.1
                        have p3175_1 := h3175c.2.1
                        have p3175_2 := h3175c.2.2.1
                        have p3175_3 := h3175c.2.2.2
                        linarith only [hlam, p3175_0]
                    · linarith only [h2134, h2135, h3174, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2135, h3131, h3133, h3134, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3205 | h3205
            · linarith only [h2134, h3084, h3133, h3205, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3207 | h3207
              · linarith only [h3129, h3131, h3132, h3133, h3207, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3209 | h3209
                · linarith only [h0, h2134, h3133, h3207, h3209, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3211 | h3211
                  · linarith only [h0, h2134, h3133, h3209, h3211, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3213 | h3213
                    · rcases h2bigk with h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c | h3214c
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h0, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h0, h3205, h3209, h3213, hc23, hc34, hlam, hphi, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h2135, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3084, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3205, h3209, h3213, hc02, hc34, hlam, hphi, ht23, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3205, h3209, h3213, hc23, hc34, hlam, hphi, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3133, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3205, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h2134, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3132, hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3209, hlam, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3211, hlam, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h2134, h3209, hc23, hc34, hlam, hphi, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3209, hc12, hc34, hlam, hphi, ht23, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3209, hc23, hc34, hlam, hphi, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [hlam, p3214_0]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3205, h3209, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3214_1, u5ehi1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h2134, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h0, h3211, hc01, hc35, hlam, hphi, ht12, ht23, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3211, hc23, hc35, hlam, hphi, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [h3213, hlam, p3214_1]
                      · have p3214_0 := h3214c.1
                        have p3214_1 := h3214c.2.1
                        have p3214_2 := h3214c.2.2.1
                        have p3214_3 := h3214c.2.2.2
                        linarith only [hlam, p3214_0]
                    · linarith only [h2134, h2135, h3213, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h2134, h2135, h3132, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3242 | h3242
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3243 | h3243
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3244 | h3244
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3245 | h3245
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3246 | h3246
                · linarith only [h2134, h2135, h3129, h3246, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3248 | h3248
                  · linarith only [h2134, h2135, h3242, h3245, h3246, h3248, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3250 | h3250
                    · linarith only [h2134, h2135, h3131, h3242, h3245, h3246, h3250, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2134, h2135, h3250, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3253 | h3253
                · linarith only [h2134, h2135, h3245, h3253, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3255 | h3255
                  · linarith only [h2134, h2135, h3243, h3255, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3257 | h3257
                    · linarith only [h2134, h2135, h3131, h3243, h3257, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2134, h2135, h3257, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2134, h2135, h3243, h3244, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3261 | h3261
            · linarith only [h2134, h3084, h3243, h3261, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3263 | h3263
              · linarith only [h3242, h3243, h3263, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3265 | h3265
                · linarith only [h0, h2134, h3261, h3263, h3265, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3267 | h3267
                  · linarith only [h2134, h2135, h3131, h3267, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3269 | h3269
                    · linarith only [h2134, h2135, h3131, h3265, h3269, hc23, hc34, hlam, hphi]
                    · linarith only [h2134, h2135, h3269, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h2134, h2135, h3242, hc01, hc24, hlam, hphi, ht12]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2135 | h2135
  · exact r1l7_22_15_H_I_L_R_x1_x0_x0 m hb2 hb5 h0 h2134 h2135
  · exact r1l7_22_15_H_I_L_R_x1_x0_x1 m hb2 hb5 h0 h2134 h2135

end R2N4
