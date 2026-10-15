import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2272 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2273 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2274 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 2 3 4 (by decide) (by decide) with h2618 | h2618
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2619 | h2619
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2620 | h2620
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2621 | h2621
        · linarith only [h1, h1951, h2272, h2274, h2621, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases h1bigk with h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h0, h1951, h2274, h2618, h2620, h4, hlam, p2623_2]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            rcases p2623_3 (m.d 0 1) (by simp) with h2626 | h2626
            · rcases p2623_3 (m.d 1 2) (by simp) with h2627 | h2627
              · linarith only [h0, h2627, hlam]
              · rcases p2623_3 (m.d 1 3) (by simp) with h2629 | h2629
                · linarith only [h2629, hlam, p2623_0]
                · rcases p2623_3 (m.d 1 4) (by simp) with h2631 | h2631
                  · linarith only [h2, h2631, hlam]
                  · rcases p2623_3 (m.d 1 5) (by simp) with h2633 | h2633
                    · linarith only [h2633, h3, hlam]
                    · rcases h3bigk with h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c | h2635c
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        rcases p2635_3 (m.d 0 3) (by simp) with h2637 | h2637
                        · rcases p2635_3 (m.d 1 3) (by simp) with h2638 | h2638
                          · linarith only [h1, h2638, hlam]
                          · rcases p2635_3 (m.d 2 3) (by simp) with h2640 | h2640
                            · linarith only [h2640, h4, hlam]
                            · linarith only [h10, h2640, hlam]
                        · linarith only [h1, h2637, hlam]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h0, h1951, h2274, h2618, h2620, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        rcases p2635_3 (m.d 0 3) (by simp) with h2645 | h2645
                        · rcases p2635_3 (m.d 1 3) (by simp) with h2646 | h2646
                          · linarith only [h1, h2646, hlam]
                          · linarith only [h2272, h2646, hlam]
                        · linarith only [h2645, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        rcases p2635_3 (m.d 0 3) (by simp) with h2650 | h2650
                        · rcases p2635_3 (m.d 1 3) (by simp) with h2651 | h2651
                          · linarith only [h1, h2651, hlam]
                          · linarith only [h2273, h2651, hlam]
                        · linarith only [h2650, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h1, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h10, hlam, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2623_1, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2621, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2623_1, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h4, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h0, h4, hlam, p2623_2, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        rcases p2635_3 (m.d 0 3) (by simp) with h2663 | h2663
                        · rcases p2635_3 (m.d 1 3) (by simp) with h2664 | h2664
                          · linarith only [h10, h2664, hlam]
                          · linarith only [h2272, h2664, hlam]
                        · linarith only [h2663, h7, hlam]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        rcases p2635_3 (m.d 0 3) (by simp) with h2668 | h2668
                        · rcases p2635_3 (m.d 1 3) (by simp) with h2669 | h2669
                          · linarith only [h10, h2669, hlam]
                          · linarith only [h2273, h2669, hlam]
                        · linarith only [h2668, h8, hlam]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h7, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2272, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2618, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2621, hlam, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h8, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2273, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2619, hlam, p2635_0]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2623_1, p2635_1]
                      · have p2635_0 := h2635c.1
                        have p2635_1 := h2635c.2.1
                        have p2635_2 := h2635c.2.2.1
                        have p2635_3 := h2635c.2.2.2
                        linarith only [hlam, p2635_0]
            · linarith only [h2626, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h0, h2274, h2620, h5, hlam, p2623_2]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            rcases p2623_3 (m.d 0 1) (by simp) with h2685 | h2685
            · rcases p2623_3 (m.d 1 2) (by simp) with h2686 | h2686
              · linarith only [h0, h2686, hlam]
              · rcases p2623_3 (m.d 1 3) (by simp) with h2688 | h2688
                · linarith only [h1, h2688, hlam]
                · linarith only [h2273, h2688, hlam]
            · linarith only [h2685, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h0, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h10, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h1951, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h2201, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h1, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            rcases p2623_3 (m.d 0 1) (by simp) with h2698 | h2698
            · rcases p2623_3 (m.d 1 2) (by simp) with h2699 | h2699
              · linarith only [h10, h2699, hlam]
              · rcases p2623_3 (m.d 1 3) (by simp) with h2701 | h2701
                · rcases p2623_3 (m.d 1 4) (by simp) with h2702 | h2702
                  · linarith only [h2272, h2702, hlam]
                  · linarith only [h1951, h2702, hlam]
                · linarith only [h10, h2701, hlam]
            · linarith only [h0, h2698, hlam]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            rcases p2623_3 (m.d 0 1) (by simp) with h2708 | h2708
            · rcases p2623_3 (m.d 1 2) (by simp) with h2709 | h2709
              · linarith only [h10, h2709, hlam]
              · rcases p2623_3 (m.d 1 3) (by simp) with h2711 | h2711
                · rcases p2623_3 (m.d 1 4) (by simp) with h2712 | h2712
                  · linarith only [h2272, h2712, hlam]
                  · rcases p2623_3 (m.d 1 5) (by simp) with h2714 | h2714
                    · linarith only [h2273, h2714, hlam]
                    · linarith only [h2274, h2714, hlam]
                · linarith only [h2272, h2711, hlam]
            · linarith only [h2, h2708, hlam]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            rcases p2623_3 (m.d 0 1) (by simp) with h2719 | h2719
            · rcases p2623_3 (m.d 1 2) (by simp) with h2720 | h2720
              · linarith only [h10, h2720, hlam]
              · rcases p2623_3 (m.d 1 3) (by simp) with h2722 | h2722
                · rcases p2623_3 (m.d 1 4) (by simp) with h2723 | h2723
                  · linarith only [h2272, h2723, hlam]
                  · rcases p2623_3 (m.d 1 5) (by simp) with h2725 | h2725
                    · linarith only [h2273, h2725, hlam]
                    · rcases h3bigk with h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h2274, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p2623_1, p2727_1]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h0, h10, h2274, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2623_1, p2727_1]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        rcases p2727_3 (m.d 0 3) (by simp) with h2731 | h2731
                        · rcases p2727_3 (m.d 1 3) (by simp) with h2732 | h2732
                          · linarith only [h1, h2732, hlam]
                          · linarith only [h2272, h2732, hlam]
                        · linarith only [h2731, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        rcases p2727_3 (m.d 0 3) (by simp) with h2736 | h2736
                        · rcases p2727_3 (m.d 1 3) (by simp) with h2737 | h2737
                          · linarith only [h1, h2737, hlam]
                          · linarith only [h2273, h2737, hlam]
                        · linarith only [h2736, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h1, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h10, hlam, p2727_1]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        rcases p2727_3 (m.d 0 3) (by simp) with h2744 | h2744
                        · rcases p2727_3 (m.d 1 3) (by simp) with h2745 | h2745
                          · rcases p2727_3 (m.d 2 3) (by simp) with h2746 | h2746
                            · rcases p2727_3 (m.d 3 4) (by simp) with h2747 | h2747
                              · linarith only [h2747, hlam, p2727_0]
                              · rcases p2727_3 (m.d 3 5) (by simp) with h2749 | h2749
                                · linarith only [h2273, h2749, hlam]
                                · linarith only [h2621, h2749, hlam]
                            · linarith only [h2618, h2746, hlam]
                          · linarith only [h2745, hlam, p2727_0]
                        · linarith only [h2744, h7, hlam]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        rcases p2727_3 (m.d 0 3) (by simp) with h2755 | h2755
                        · rcases p2727_3 (m.d 1 3) (by simp) with h2756 | h2756
                          · rcases p2727_3 (m.d 2 3) (by simp) with h2757 | h2757
                            · rcases p2727_3 (m.d 3 4) (by simp) with h2758 | h2758
                              · linarith only [h2272, h2758, hlam]
                              · rcases p2727_3 (m.d 3 5) (by simp) with h2760 | h2760
                                · linarith only [h2760, hlam, p2727_0]
                                · rcases h5bigk with h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    rcases p2762_3 (m.d 0 5) (by simp) with h2764 | h2764
                                    · rcases p2762_3 (m.d 1 5) (by simp) with h2765 | h2765
                                      · linarith only [h2765, h3, hlam]
                                      · rcases p2762_3 (m.d 2 5) (by simp) with h2767 | h2767
                                        · linarith only [h2767, h6, hlam]
                                        · linarith only [h2201, h2767, hlam]
                                    · linarith only [h2764, h3, hlam]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2201, h7, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    rcases p2762_3 (m.d 0 5) (by simp) with h2772 | h2772
                                    · rcases p2762_3 (m.d 1 5) (by simp) with h2773 | h2773
                                      · linarith only [h2773, h3, hlam]
                                      · linarith only [h2273, h2773, hlam]
                                    · linarith only [h2772, h8, hlam]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h0, h1951, h2274, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h3, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2201, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p2623_1, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2274, hlam, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h6, hlam, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h1951, h2274, hc12, hc25, hlam, hphi, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h0, h2619, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h0, h1951, h2274, h2618, h2620, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h8, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2273, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2619, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2621, hlam, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h9, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h2620, hlam, p2762_0]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [h0, h2618, h2620, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2762_1]
                                  · have p2762_0 := h2762c.1
                                    have p2762_1 := h2762c.2.1
                                    have p2762_2 := h2762c.2.2.1
                                    have p2762_3 := h2762c.2.2.2
                                    linarith only [hlam, p2762_0]
                            · linarith only [h2619, h2757, hlam]
                          · linarith only [h2756, hlam, p2727_0]
                        · linarith only [h2755, h8, hlam]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h4, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h0, h2272, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2727_1]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        rcases p2727_3 (m.d 0 3) (by simp) with h2804 | h2804
                        · rcases p2727_3 (m.d 1 3) (by simp) with h2805 | h2805
                          · linarith only [h10, h2805, hlam]
                          · linarith only [h2272, h2805, hlam]
                        · linarith only [h2804, h7, hlam]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        rcases p2727_3 (m.d 0 3) (by simp) with h2809 | h2809
                        · rcases p2727_3 (m.d 1 3) (by simp) with h2810 | h2810
                          · linarith only [h10, h2810, hlam]
                          · linarith only [h2273, h2810, hlam]
                        · linarith only [h2809, h8, hlam]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h7, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h2272, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h2618, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h2621, hlam, p2727_1]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h8, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h2273, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h2619, hlam, p2727_0]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [h1, h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2727_1]
                      · have p2727_0 := h2727c.1
                        have p2727_1 := h2727c.2.1
                        have p2727_2 := h2727c.2.2.1
                        have p2727_3 := h2727c.2.2.2
                        linarith only [hlam, p2727_0]
                · linarith only [h2273, h2722, hlam]
            · linarith only [h2719, h3, hlam]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h2, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h0, h2274, h2618, h2620, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2623_1]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h2272, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h2274, hlam, p2623_1]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h3, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h0, h2274, h2618, h2620, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2623_1]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h2273, hlam, p2623_0]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [h0, h2274, h2618, h2620, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2623_1]
          · have p2623_0 := h2623c.1
            have p2623_1 := h2623c.2.1
            have p2623_2 := h2623c.2.2.1
            have p2623_3 := h2623c.2.2.2
            linarith only [hlam, p2623_0]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2836 | h2836
        · linarith only [h0, h1951, h2620, h2836, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases h1bigk with h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h0, h1951, h2620, h4, h7, h9, hlam, p2838_2]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h2841 | h2841
            · rcases p2838_3 (m.d 1 2) (by simp) with h2842 | h2842
              · linarith only [h0, h2842, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h2844 | h2844
                · linarith only [h2844, hlam, p2838_0]
                · rcases p2838_3 (m.d 1 4) (by simp) with h2846 | h2846
                  · linarith only [h2, h2846, hlam]
                  · rcases p2838_3 (m.d 1 5) (by simp) with h2848 | h2848
                    · linarith only [h2848, h3, hlam]
                    · rcases h3bigk with h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c | h2850c
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        rcases p2850_3 (m.d 0 3) (by simp) with h2852 | h2852
                        · rcases p2850_3 (m.d 1 3) (by simp) with h2853 | h2853
                          · linarith only [h1, h2853, hlam]
                          · rcases p2850_3 (m.d 2 3) (by simp) with h2855 | h2855
                            · linarith only [h2855, h4, hlam]
                            · linarith only [h10, h2855, hlam]
                        · linarith only [h1, h2852, hlam]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        rcases p2850_3 (m.d 0 3) (by simp) with h2859 | h2859
                        · rcases p2850_3 (m.d 1 3) (by simp) with h2860 | h2860
                          · linarith only [h1, h2860, hlam]
                          · rcases p2850_3 (m.d 2 3) (by simp) with h2862 | h2862
                            · linarith only [h2862, h4, hlam]
                            · rcases p2850_3 (m.d 3 4) (by simp) with h2864 | h2864
                              · linarith only [h2864, h7, hlam]
                              · rcases p2850_3 (m.d 3 5) (by simp) with h2866 | h2866
                                · linarith only [h2866, h8, hlam]
                                · rcases h5bigk with h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    rcases p2868_3 (m.d 0 5) (by simp) with h2870 | h2870
                                    · rcases p2868_3 (m.d 1 5) (by simp) with h2871 | h2871
                                      · linarith only [h2871, h3, hlam]
                                      · rcases p2868_3 (m.d 2 5) (by simp) with h2873 | h2873
                                        · linarith only [h2873, h6, hlam]
                                        · linarith only [h2201, h2873, hlam]
                                    · linarith only [h2870, h3, hlam]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h0, h1951, h2620, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    rcases p2868_3 (m.d 0 5) (by simp) with h2878 | h2878
                                    · rcases p2868_3 (m.d 1 5) (by simp) with h2879 | h2879
                                      · linarith only [h2879, h3, hlam]
                                      · linarith only [h2273, h2879, hlam]
                                    · linarith only [h2878, h8, hlam]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h0, h1951, h2620, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h3, hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h2201, hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h2274, hlam, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h6, hlam, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h0, h2619, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h0, h2619, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2850_1, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h2620, hlam, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h8, hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h2273, hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h2619, hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h2836, hlam, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h9, hlam, p2868_0]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h1951, h2274, hc12, hc45, hlam, hphi, ht23, ht34, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p2868_1]
                                  · have p2868_0 := h2868c.1
                                    have p2868_1 := h2868c.2.1
                                    have p2868_2 := h2868c.2.2.1
                                    have p2868_3 := h2868c.2.2.2
                                    linarith only [hlam, p2868_0]
                        · linarith only [h2859, h4, hlam]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        rcases p2850_3 (m.d 0 3) (by simp) with h2905 | h2905
                        · rcases p2850_3 (m.d 1 3) (by simp) with h2906 | h2906
                          · linarith only [h1, h2906, hlam]
                          · linarith only [h2272, h2906, hlam]
                        · linarith only [h2905, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        rcases p2850_3 (m.d 0 3) (by simp) with h2910 | h2910
                        · rcases p2850_3 (m.d 1 3) (by simp) with h2911 | h2911
                          · linarith only [h1, h2911, hlam]
                          · linarith only [h2273, h2911, hlam]
                        · linarith only [h2910, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h1, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h10, hlam, p2850_1]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2838_1, p2850_1]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2836, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2838_1, p2850_1]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h4, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h0, h4, hlam, p2838_2, p2850_1]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        rcases p2850_3 (m.d 0 3) (by simp) with h2923 | h2923
                        · rcases p2850_3 (m.d 1 3) (by simp) with h2924 | h2924
                          · linarith only [h10, h2924, hlam]
                          · linarith only [h2272, h2924, hlam]
                        · linarith only [h2923, h7, hlam]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        rcases p2850_3 (m.d 0 3) (by simp) with h2928 | h2928
                        · rcases p2850_3 (m.d 1 3) (by simp) with h2929 | h2929
                          · linarith only [h10, h2929, hlam]
                          · linarith only [h2273, h2929, hlam]
                        · linarith only [h2928, h8, hlam]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h7, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2272, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2618, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2836, hlam, p2850_1]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h8, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2273, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2619, hlam, p2850_0]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2838_1, p2850_1]
                      · have p2850_0 := h2850c.1
                        have p2850_1 := h2850c.2.1
                        have p2850_2 := h2850c.2.2.1
                        have p2850_3 := h2850c.2.2.2
                        linarith only [hlam, p2850_0]
            · linarith only [h2841, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h2944 | h2944
            · rcases p2838_3 (m.d 1 2) (by simp) with h2945 | h2945
              · linarith only [h0, h2945, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h2947 | h2947
                · linarith only [h1, h2947, hlam]
                · linarith only [h2272, h2947, hlam]
            · linarith only [h2944, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h2951 | h2951
            · rcases p2838_3 (m.d 1 2) (by simp) with h2952 | h2952
              · linarith only [h0, h2952, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h2954 | h2954
                · linarith only [h1, h2954, hlam]
                · linarith only [h2273, h2954, hlam]
            · linarith only [h2951, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h0, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h10, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h1951, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h2201, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h1, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h2964 | h2964
            · rcases p2838_3 (m.d 1 2) (by simp) with h2965 | h2965
              · linarith only [h10, h2965, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h2967 | h2967
                · rcases p2838_3 (m.d 1 4) (by simp) with h2968 | h2968
                  · linarith only [h2272, h2968, hlam]
                  · linarith only [h1951, h2968, hlam]
                · linarith only [h10, h2967, hlam]
            · linarith only [h0, h2964, hlam]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h2974 | h2974
            · rcases p2838_3 (m.d 1 2) (by simp) with h2975 | h2975
              · linarith only [h10, h2975, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h2977 | h2977
                · rcases p2838_3 (m.d 1 4) (by simp) with h2978 | h2978
                  · linarith only [h2272, h2978, hlam]
                  · rcases p2838_3 (m.d 1 5) (by simp) with h2980 | h2980
                    · linarith only [h2273, h2980, hlam]
                    · linarith only [h2274, h2980, hlam]
                · linarith only [h2272, h2977, hlam]
            · linarith only [h2, h2974, hlam]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h2985 | h2985
            · rcases p2838_3 (m.d 1 2) (by simp) with h2986 | h2986
              · linarith only [h10, h2986, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h2988 | h2988
                · rcases p2838_3 (m.d 1 4) (by simp) with h2989 | h2989
                  · linarith only [h2272, h2989, hlam]
                  · rcases p2838_3 (m.d 1 5) (by simp) with h2991 | h2991
                    · linarith only [h2273, h2991, hlam]
                    · rcases h3bigk with h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h0, h2274, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2838_1, p2993_1]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h0, h10, h2274, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2838_1, p2993_1]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        rcases p2993_3 (m.d 0 3) (by simp) with h2997 | h2997
                        · rcases p2993_3 (m.d 1 3) (by simp) with h2998 | h2998
                          · linarith only [h1, h2998, hlam]
                          · linarith only [h2272, h2998, hlam]
                        · linarith only [h2997, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        rcases p2993_3 (m.d 0 3) (by simp) with h3002 | h3002
                        · rcases p2993_3 (m.d 1 3) (by simp) with h3003 | h3003
                          · linarith only [h1, h3003, hlam]
                          · linarith only [h2273, h3003, hlam]
                        · linarith only [h3002, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h1, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h10, hlam, p2993_1]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        rcases p2993_3 (m.d 0 3) (by simp) with h3010 | h3010
                        · rcases p2993_3 (m.d 1 3) (by simp) with h3011 | h3011
                          · rcases p2993_3 (m.d 2 3) (by simp) with h3012 | h3012
                            · rcases p2993_3 (m.d 3 4) (by simp) with h3013 | h3013
                              · linarith only [h3013, hlam, p2993_0]
                              · rcases p2993_3 (m.d 3 5) (by simp) with h3015 | h3015
                                · linarith only [h2273, h3015, hlam]
                                · linarith only [h2836, h3015, hlam]
                            · linarith only [h2618, h3012, hlam]
                          · linarith only [h3011, hlam, p2993_0]
                        · linarith only [h3010, h7, hlam]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        rcases p2993_3 (m.d 0 3) (by simp) with h3021 | h3021
                        · rcases p2993_3 (m.d 1 3) (by simp) with h3022 | h3022
                          · rcases p2993_3 (m.d 2 3) (by simp) with h3023 | h3023
                            · rcases p2993_3 (m.d 3 4) (by simp) with h3024 | h3024
                              · linarith only [h2272, h3024, hlam]
                              · rcases p2993_3 (m.d 3 5) (by simp) with h3026 | h3026
                                · linarith only [h3026, hlam, p2993_0]
                                · rcases h5bigk with h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c | h3028c
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    rcases p3028_3 (m.d 0 5) (by simp) with h3030 | h3030
                                    · rcases p3028_3 (m.d 1 5) (by simp) with h3031 | h3031
                                      · linarith only [h3, h3031, hlam]
                                      · rcases p3028_3 (m.d 2 5) (by simp) with h3033 | h3033
                                        · linarith only [h3033, h6, hlam]
                                        · linarith only [h2201, h3033, hlam]
                                    · linarith only [h3, h3030, hlam]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h1951, h2620, h7, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    rcases p3028_3 (m.d 0 5) (by simp) with h3038 | h3038
                                    · rcases p3028_3 (m.d 1 5) (by simp) with h3039 | h3039
                                      · linarith only [h3, h3039, hlam]
                                      · linarith only [h2273, h3039, hlam]
                                    · linarith only [h3038, h8, hlam]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h0, h1951, h2274, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h3, hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h2201, hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p2838_1, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h2274, hlam, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h6, hlam, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h0, h2619, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h2620, hlam, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h8, hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h2273, hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h2619, hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h2836, hlam, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h9, hlam, p3028_0]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h1951, h2274, hc12, hc45, hlam, hphi, ht23, ht34, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p3028_1]
                                  · have p3028_0 := h3028c.1
                                    have p3028_1 := h3028c.2.1
                                    have p3028_2 := h3028c.2.2.1
                                    have p3028_3 := h3028c.2.2.2
                                    linarith only [hlam, p3028_0]
                            · linarith only [h2619, h3023, hlam]
                          · linarith only [h3022, hlam, p2993_0]
                        · linarith only [h3021, h8, hlam]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h4, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h0, h2272, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2993_1]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        rcases p2993_3 (m.d 0 3) (by simp) with h3070 | h3070
                        · rcases p2993_3 (m.d 1 3) (by simp) with h3071 | h3071
                          · linarith only [h10, h3071, hlam]
                          · linarith only [h2272, h3071, hlam]
                        · linarith only [h3070, h7, hlam]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        rcases p2993_3 (m.d 0 3) (by simp) with h3075 | h3075
                        · rcases p2993_3 (m.d 1 3) (by simp) with h3076 | h3076
                          · linarith only [h10, h3076, hlam]
                          · linarith only [h2273, h3076, hlam]
                        · linarith only [h3075, h8, hlam]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h7, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h2272, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h2618, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h2836, hlam, p2993_1]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h8, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h2273, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h2619, hlam, p2993_0]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [h1, h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2993_1]
                      · have p2993_0 := h2993c.1
                        have p2993_1 := h2993c.2.1
                        have p2993_2 := h2993c.2.2.1
                        have p2993_3 := h2993c.2.2.2
                        linarith only [hlam, p2993_0]
                · linarith only [h2273, h2988, hlam]
            · linarith only [h2985, h3, hlam]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h2, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h0, h2274, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2838_1]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h2272, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h2274, hlam, p2838_1]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h3, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h3098 | h3098
            · rcases p2838_3 (m.d 1 2) (by simp) with h3099 | h3099
              · linarith only [h2201, h3099, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h3101 | h3101
                · rcases p2838_3 (m.d 1 4) (by simp) with h3102 | h3102
                  · linarith only [h2274, h3102, hlam]
                  · linarith only [h1951, h3102, hlam]
                · linarith only [h10, h3101, hlam]
            · linarith only [h0, h3098, hlam]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [h2273, hlam, p2838_0]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            rcases p2838_3 (m.d 0 1) (by simp) with h3108 | h3108
            · rcases p2838_3 (m.d 1 2) (by simp) with h3109 | h3109
              · linarith only [h2201, h3109, hlam]
              · rcases p2838_3 (m.d 1 3) (by simp) with h3111 | h3111
                · rcases p2838_3 (m.d 1 4) (by simp) with h3112 | h3112
                  · linarith only [h2274, h3112, hlam]
                  · rcases p2838_3 (m.d 1 5) (by simp) with h3114 | h3114
                    · rcases h3bigk with h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c | h3115c
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h0, h1951, h2273, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2838_1, p3115_1]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h0, h10, h1951, h2273, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2838_1, p3115_1]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h2272, h2274, h7, h9, hlam, p2838_1, p3115_2]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        rcases p3115_3 (m.d 0 3) (by simp) with h3120 | h3120
                        · rcases p3115_3 (m.d 1 3) (by simp) with h3121 | h3121
                          · linarith only [h1, h3121, hlam]
                          · linarith only [h2273, h3121, hlam]
                        · linarith only [h3120, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h1, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h10, hlam, p3115_1]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        rcases p3115_3 (m.d 0 3) (by simp) with h3128 | h3128
                        · rcases p3115_3 (m.d 1 3) (by simp) with h3129 | h3129
                          · rcases p3115_3 (m.d 2 3) (by simp) with h3130 | h3130
                            · rcases p3115_3 (m.d 3 4) (by simp) with h3131 | h3131
                              · linarith only [h3131, hlam, p3115_0]
                              · rcases p3115_3 (m.d 3 5) (by simp) with h3133 | h3133
                                · linarith only [h2273, h3133, hlam]
                                · linarith only [h2836, h3133, hlam]
                            · linarith only [h2618, h3130, hlam]
                          · linarith only [h3129, hlam, p3115_0]
                        · linarith only [h3128, h7, hlam]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        rcases p3115_3 (m.d 0 3) (by simp) with h3139 | h3139
                        · rcases p3115_3 (m.d 1 3) (by simp) with h3140 | h3140
                          · rcases p3115_3 (m.d 2 3) (by simp) with h3141 | h3141
                            · rcases p3115_3 (m.d 3 4) (by simp) with h3142 | h3142
                              · linarith only [h2272, h3142, hlam]
                              · rcases p3115_3 (m.d 3 5) (by simp) with h3144 | h3144
                                · linarith only [h3144, hlam, p3115_0]
                                · rcases h5bigk with h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2838_1, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h2201, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    rcases p3146_3 (m.d 0 5) (by simp) with h3150 | h3150
                                    · rcases p3146_3 (m.d 1 5) (by simp) with h3151 | h3151
                                      · linarith only [h3, h3151, hlam]
                                      · linarith only [h2273, h3151, hlam]
                                    · linarith only [h3150, h8, hlam]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h2620, h4, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h3, hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h2201, hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h1, h2273, hc01, hc35, hlam, hphi, ht0b, ht5b, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h2274, hlam, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h6, hlam, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h1951, hc12, hc25, hlam, hphi, p2838_1, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h2619, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h2620, hlam, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h8, hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h2273, hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h2619, hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h2836, hlam, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h9, hlam, p3146_0]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h1951, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2838_1, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p3146_1]
                                  · have p3146_0 := h3146c.1
                                    have p3146_1 := h3146c.2.1
                                    have p3146_2 := h3146c.2.2.1
                                    have p3146_3 := h3146c.2.2.2
                                    linarith only [hlam, p3146_0]
                            · linarith only [h2619, h3141, hlam]
                          · linarith only [h3140, hlam, p3115_0]
                        · linarith only [h3139, h8, hlam]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h4, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h0, h1951, h2273, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2838_1, p3115_1]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        rcases p3115_3 (m.d 0 3) (by simp) with h3182 | h3182
                        · rcases p3115_3 (m.d 1 3) (by simp) with h3183 | h3183
                          · linarith only [h10, h3183, hlam]
                          · linarith only [h2272, h3183, hlam]
                        · linarith only [h3182, h7, hlam]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        rcases p3115_3 (m.d 0 3) (by simp) with h3187 | h3187
                        · rcases p3115_3 (m.d 1 3) (by simp) with h3188 | h3188
                          · linarith only [h10, h3188, hlam]
                          · linarith only [h2273, h3188, hlam]
                        · linarith only [h3187, h8, hlam]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h7, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h2272, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h2618, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h2836, hlam, p3115_1]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h8, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h2273, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h2619, hlam, p3115_0]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [h1, h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3115_1]
                      · have p3115_0 := h3115c.1
                        have p3115_1 := h3115c.2.1
                        have p3115_2 := h3115c.2.2.1
                        have p3115_3 := h3115c.2.2.2
                        linarith only [hlam, p3115_0]
                    · linarith only [h2274, h3114, hlam]
                · linarith only [h2272, h3111, hlam]
            · linarith only [h2, h3108, hlam]
          · have p2838_0 := h2838c.1
            have p2838_1 := h2838c.2.1
            have p2838_2 := h2838c.2.2.1
            have p2838_3 := h2838c.2.2.2
            linarith only [hlam, p2838_0]
    · linarith only [h10, h2273, h2619, hlam]
  · linarith only [h10, h2272, h2618, hlam]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2272 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2273 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h2274 | h2274
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201 h2272 h2273 h2274
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201 h2272 h2273 h2274

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2272 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2273 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h3208 | h3208
  · linarith only [h2272, h2273, h3208, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h3210 | h3210
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3211 | h3211
      · linarith only [h0, h2272, h2273, h3211, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3213 | h3213
        · linarith only [h0, h3208, h3210, h3211, h3213, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h3215 | h3215
          · linarith only [h1, h2272, h3213, h3215, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases h1bigk with h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c | h3217c
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h0, h10, h3211, h3215, h4, h7, h9, hlam, p3217_2]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              rcases p3217_3 (m.d 0 1) (by simp) with h3220 | h3220
              · rcases p3217_3 (m.d 1 2) (by simp) with h3221 | h3221
                · linarith only [h0, h3221, hlam]
                · rcases p3217_3 (m.d 1 3) (by simp) with h3223 | h3223
                  · linarith only [h3223, hlam, p3217_0]
                  · rcases p3217_3 (m.d 1 4) (by simp) with h3225 | h3225
                    · linarith only [h2, h3225, hlam]
                    · rcases p3217_3 (m.d 1 5) (by simp) with h3227 | h3227
                      · linarith only [h3, h3227, hlam]
                      · linarith only [h2273, h3227, hlam]
              · linarith only [h3220, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              rcases p3217_3 (m.d 0 1) (by simp) with h3231 | h3231
              · rcases p3217_3 (m.d 1 2) (by simp) with h3232 | h3232
                · linarith only [h0, h3232, hlam]
                · rcases p3217_3 (m.d 1 3) (by simp) with h3234 | h3234
                  · linarith only [h1, h3234, hlam]
                  · linarith only [h2272, h3234, hlam]
              · linarith only [h3231, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              rcases p3217_3 (m.d 0 1) (by simp) with h3238 | h3238
              · rcases p3217_3 (m.d 1 2) (by simp) with h3239 | h3239
                · linarith only [h0, h3239, hlam]
                · rcases p3217_3 (m.d 1 3) (by simp) with h3241 | h3241
                  · linarith only [h1, h3241, hlam]
                  · rcases p3217_3 (m.d 1 4) (by simp) with h3243 | h3243
                    · linarith only [h2, h3243, hlam]
                    · rcases p3217_3 (m.d 1 5) (by simp) with h3245 | h3245
                      · linarith only [h3245, hlam, p3217_0]
                      · rcases h3bigk with h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c | h3247c
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          rcases p3247_3 (m.d 0 3) (by simp) with h3249 | h3249
                          · rcases p3247_3 (m.d 1 3) (by simp) with h3250 | h3250
                            · linarith only [h1, h3250, hlam]
                            · rcases p3247_3 (m.d 2 3) (by simp) with h3252 | h3252
                              · linarith only [h3252, h4, hlam]
                              · linarith only [h10, h3252, hlam]
                          · linarith only [h1, h3249, hlam]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          rcases p3247_3 (m.d 0 3) (by simp) with h3256 | h3256
                          · rcases p3247_3 (m.d 1 3) (by simp) with h3257 | h3257
                            · linarith only [h1, h3257, hlam]
                            · rcases p3247_3 (m.d 2 3) (by simp) with h3259 | h3259
                              · linarith only [h3259, h4, hlam]
                              · rcases p3247_3 (m.d 3 4) (by simp) with h3261 | h3261
                                · linarith only [h3261, h7, hlam]
                                · rcases p3247_3 (m.d 3 5) (by simp) with h3263 | h3263
                                  · linarith only [h3263, h8, hlam]
                                  · linarith only [h3211, h3263, hlam]
                          · linarith only [h3256, h4, hlam]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h10, h2272, h3211, h3215, h7, h9, hlam, p3247_2]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h0, h1951, h3210, h3211, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h1, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h10, hlam, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3217_1, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h2273, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h4, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h3211, hc13, hc35, hlam, hphi, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h0, h3211, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h3211, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h7, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h2272, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h3210, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h3215, hlam, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h8, hlam, p3247_0]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h0, h2272, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [h0, h10, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3247_1]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          rcases p3247_3 (m.d 0 3) (by simp) with h3287 | h3287
                          · rcases p3247_3 (m.d 1 3) (by simp) with h3288 | h3288
                            · linarith only [h2273, h3288, hlam]
                            · linarith only [h2272, h3288, hlam]
                          · linarith only [h3287, h7, hlam]
                        · have p3247_0 := h3247c.1
                          have p3247_1 := h3247c.2.1
                          have p3247_2 := h3247c.2.2.1
                          have p3247_3 := h3247c.2.2.2
                          linarith only [hlam, p3247_0]
              · linarith only [h3238, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h0, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h10, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h1951, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h2201, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h1, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h0, h2273, h3215, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3217_1]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h0, h1951, h2273, h3215, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3217_1]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h2273, hlam, p3217_1]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h2, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h0, h2272, h2273, h3215, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3217_1]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h2272, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h3208, hlam, p3217_1]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h3, hlam, p3217_0]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              rcases p3217_3 (m.d 0 1) (by simp) with h3310 | h3310
              · rcases p3217_3 (m.d 1 2) (by simp) with h3311 | h3311
                · linarith only [h2201, h3311, hlam]
                · rcases p3217_3 (m.d 1 3) (by simp) with h3313 | h3313
                  · linarith only [h2273, h3313, hlam]
                  · linarith only [h10, h3313, hlam]
              · linarith only [h0, h3310, hlam]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [h0, h2201, h2272, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3217_1]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              rcases p3217_3 (m.d 0 1) (by simp) with h3318 | h3318
              · rcases p3217_3 (m.d 1 2) (by simp) with h3319 | h3319
                · linarith only [h2201, h3319, hlam]
                · rcases p3217_3 (m.d 1 3) (by simp) with h3321 | h3321
                  · linarith only [h2273, h3321, hlam]
                  · linarith only [h2272, h3321, hlam]
              · linarith only [h2, h3318, hlam]
            · have p3217_0 := h3217c.1
              have p3217_1 := h3217c.2.1
              have p3217_2 := h3217c.2.2.1
              have p3217_3 := h3217c.2.2.2
              linarith only [hlam, p3217_0]
    · linarith only [h1, h10, h2272, h3210, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2272 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h2273 | h2273
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201 h2272 h2273
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201 h2272 h2273

end R2N4
