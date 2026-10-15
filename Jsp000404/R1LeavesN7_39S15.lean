import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2080 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2597 | h2597
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2598 | h2598
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2599 | h2599
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2600 | h2600
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2601 | h2601
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2602 | h2602
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2603 | h2603
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2604 | h2604
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2605 | h2605
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2606 | h2606
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2607 | h2607
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2608 | h2608
                        · linarith only [h2080, h2597, h2605, h2608, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h2080, h2597, h2604, h2605, h2608, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h2080, h2598, h2599, h2603, h2607, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2080, h2597, h2599, h2602, h2606, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2599, h2605, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2614 | h2614
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2615 | h2615
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2616 | h2616
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2617 | h2617
                        · linarith only [h0, h2597, h2600, h2604, h2617, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2619 | h2619
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2620 | h2620
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2621 | h2621
                              · linarith only [h2080, h2597, h2601, h2604, h2614, h2615, h2621, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases h0bigk with h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c | h2623c
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h0, hlam, p2623_1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2080, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2080, h2614, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2080, h2597, h2604, h2614, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h0, h2597, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h0, h2597, h2604, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2597, h2615, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2623_1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2599, hlam, p2623_1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2080, h2597, h2614, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2080, h2597, h2604, h2614, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2597, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2600, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2602, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2604, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2598, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2601, hlam, p2623_1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h2603, hlam, p2623_0]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [h0, h2597, h2598, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2623_1, u2elo1]
                                · have p2623_0 := h2623c.1
                                  have p2623_1 := h2623c.2.1
                                  have p2623_2 := h2623c.2.2.1
                                  have p2623_3 := h2623c.2.2.2
                                  linarith only [hlam, p2623_0]
                            · linarith only [h2080, h2598, h2614, h2616, h2620, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h2080, h2597, h2614, h2615, h2619, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h2080, h2603, h2616, hlam]
                    · linarith only [h2080, h2602, h2615, hlam]
                  · linarith only [h0, h2614, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2080, h2598, h2603, hlam]
            · linarith only [h2080, h2597, h2602, hlam]
          · linarith only [h2080, h2598, h2599, h2601, hlam]
        · linarith only [h2080, h2597, h2599, h2600, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2658 | h2658
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2659 | h2659
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2660 | h2660
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2661 | h2661
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2662 | h2662
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2663 | h2663
                  · linarith only [h2599, h2663, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2663, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2666 | h2666
                  · linarith only [h0, h2597, h2599, h2666, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2597, h2666, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h0, h2598, h2599, h2661, hlam]
            · linarith only [h0, h2597, h2599, h2660, hlam]
          · linarith only [h0, h2598, h2659, hlam]
        · linarith only [h0, h2597, h2658, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2673 | h2673
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2674 | h2674
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2675 | h2675
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2676 | h2676
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2677 | h2677
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2678 | h2678
                · linarith only [h2597, h2598, h2678, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2680 | h2680
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2681 | h2681
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2682 | h2682
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2683 | h2683
                        · linarith only [h2597, h2598, h2678, h2680, h2682, h2683, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2685 | h2685
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2686 | h2686
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2687 | h2687
                              · linarith only [h2597, h2598, h2681, h2683, h2687, hlam]
                              · rcases h0bigk with h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c | h2689c
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h0, hlam, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2080, hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2598, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2598, hlam, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h0, h2597, h2681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2597, h2681, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2673, hlam, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2080, h2597, h2680, h2681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2080, h2597, h2598, h2680, h2681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2597, hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2674, hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2676, hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2678, hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2597, h2681, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2675, hlam, p2689_1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2677, hlam, p2689_0]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [h2080, h2597, h2677, h2680, h2681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2689_1, u2elo1]
                                · have p2689_0 := h2689c.1
                                  have p2689_1 := h2689c.2.1
                                  have p2689_2 := h2689c.2.2.1
                                  have p2689_3 := h2689c.2.2.2
                                  linarith only [hlam, p2689_0]
                            · linarith only [h2080, h2677, h2680, h2685, h2686, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h0, h2597, h2681, h2685, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h2080, h2677, h2682, hlam]
                    · linarith only [h2080, h2676, h2681, hlam]
                  · linarith only [h0, h2680, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2720 | h2720
                · linarith only [h2080, h2597, h2677, h2720, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2722 | h2722
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2723 | h2723
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2724 | h2724
                      · linarith only [h2080, h2597, h2677, h2722, h2723, h2724, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2726 | h2726
                        · linarith only [h0, h2597, h2674, h2720, h2726, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2728 | h2728
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2729 | h2729
                            · linarith only [h0, h2080, h2673, h2724, h2729, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2731 | h2731
                              · linarith only [h2080, h2597, h2723, h2724, h2726, h2731, hlam]
                              · linarith only [h2080, h2597, h2723, h2724, h2731, hc34, hc45, hlam, hphi]
                          · linarith only [h2080, h2597, h2723, h2724, h2728, hc23, hc35, hlam, hphi]
                    · linarith only [h2080, h2597, h2676, h2677, h2723, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2597, h2722, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h2080, h2597, h2676, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2738 | h2738
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2739 | h2739
              · linarith only [h2673, h2675, h2739, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2741 | h2741
                · linarith only [h2080, h2597, h2673, h2675, h2741, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2743 | h2743
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2744 | h2744
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2745 | h2745
                      · linarith only [h2080, h2597, h2739, h2743, h2744, h2745, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2747 | h2747
                        · linarith only [h2080, h2597, h2673, h2675, h2741, h2747, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2749 | h2749
                          · linarith only [h2673, h2675, h2749, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · linarith only [h2080, h2597, h2744, h2745, h2749, hc23, hc35, hlam, hphi]
                    · linarith only [h2080, h2673, h2675, h2738, h2744, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2597, h2743, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h2080, h2597, h2738, hlam]
        · linarith only [h0, h2597, h2674, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2756 | h2756
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2757 | h2757
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2758 | h2758
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2759 | h2759
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2760 | h2760
                · linarith only [h2597, h2598, h2760, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2762 | h2762
                  · linarith only [h2598, h2673, h2757, h2762, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2597, h2762, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h2673, h2757, h2759, hlam]
            · linarith only [h2597, h2598, h2673, h2757, h2758, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2767 | h2767
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2768 | h2768
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2769 | h2769
                · linarith only [h0, h2597, h2757, h2769, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2771 | h2771
                  · linarith only [h0, h2597, h2673, h2771, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2597, h2771, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2774 | h2774
                · linarith only [h2080, h2597, h2768, h2774, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2776 | h2776
                  · linarith only [h0, h2597, h2673, h2776, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2597, h2776, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h2597, h2673, h2767, hlam]
        · linarith only [h0, h2597, h2756, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2781 | h2781
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2782 | h2782
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2783 | h2783
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2784 | h2784
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2785 | h2785
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2786 | h2786
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2787 | h2787
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2788 | h2788
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2789 | h2789
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2790 | h2790
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2791 | h2791
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2792 | h2792
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2793 | h2793
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2794 | h2794
                              · linarith only [h2782, h2792, h2794, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h2781, h2791, h2794, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h2597, h2781, h2788, h2789, h2790, h2793, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2798 | h2798
                            · linarith only [h0, h2782, h2785, h2792, h2798, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h2597, h2781, h2788, h2789, h2790, h2798, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h2597, h2782, h2785, h2787, h2791, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h2080, h2786, h2790, hlam]
                    · linarith only [h2080, h2785, h2789, hlam]
                  · linarith only [h0, h2781, h2788, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2597, h2781, h2787, hlam]
              · linarith only [h2080, h2781, h2786, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2807 | h2807
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2808 | h2808
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2809 | h2809
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2810 | h2810
                    · linarith only [h2080, h2785, h2809, h2810, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2812 | h2812
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2813 | h2813
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2814 | h2814
                          · linarith only [h2080, h2781, h2782, h2810, h2812, h2814, hc03, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2816 | h2816
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2817 | h2817
                              · rcases h0bigk with h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2080, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2597, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2080, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2818_1, u2elo1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2818_1, u2elo1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2818_1, u2elo1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, h2784, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2818_1, u2elo1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2781, hc03, hc15, hlam, hphi, ht0b, ht5b, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2782, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2785, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2080, h2784, h2810, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2781, hc04, hc15, hlam, hphi, ht0b, ht5b, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2783, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, h2783, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2818_1, u2elo1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, h2783, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2818_1, u2elo1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2781, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2784, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2807, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2808, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                              · linarith only [h2080, h2781, h2810, h2812, h2817, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h2080, h2781, h2810, h2812, h2816, hc23, hc34, hlam, hphi]
                        · linarith only [h2597, h2781, h2808, h2813, hlam]
                      · linarith only [h2080, h2781, h2807, h2812, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2781, h2809, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2080, h2781, h2785, h2808, hlam]
              · linarith only [h2080, h2781, h2807, hlam]
          · linarith only [h2597, h2781, h2783, h2784, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2852 | h2852
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2853 | h2853
            · linarith only [h2782, h2783, h2853, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2855 | h2855
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2856 | h2856
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2857 | h2857
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2858 | h2858
                    · linarith only [h2080, h2853, h2857, h2858, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2860 | h2860
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2861 | h2861
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2862 | h2862
                          · linarith only [h2080, h2781, h2858, h2860, h2862, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2864 | h2864
                            · linarith only [h2782, h2783, h2864, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                            · linarith only [h2080, h2781, h2858, h2860, h2864, hc23, hc34, hlam, hphi]
                        · linarith only [h2080, h2781, h2856, h2858, h2860, h2861, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2080, h2782, h2783, h2855, h2860, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2781, h2857, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2597, h2781, h2856, hlam]
              · linarith only [h2080, h2781, h2855, hlam]
          · linarith only [h0, h2781, h2852, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2873 | h2873
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2874 | h2874
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2875 | h2875
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2876 | h2876
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2877 | h2877
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2878 | h2878
                  · linarith only [h2597, h2782, h2873, h2878, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2781, h2878, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2597, h2781, h2877, hlam]
              · linarith only [h2597, h2781, h2782, h2873, h2876, hlam]
            · linarith only [h2782, h2873, h2875, hlam]
          · linarith only [h2597, h2781, h2873, h2874, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2885 | h2885
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2886 | h2886
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2887 | h2887
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2888 | h2888
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2889 | h2889
                  · linarith only [h2782, h2889, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2781, h2889, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h2781, h2873, h2888, hlam]
              · linarith only [h0, h2781, h2873, h2886, h2887, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2894 | h2894
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2895 | h2895
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2896 | h2896
                  · linarith only [h0, h2781, h2782, h2896, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h2781, h2896, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2080, h2781, h2886, h2895, hlam]
              · linarith only [h0, h2781, h2782, h2894, hlam]
          · linarith only [h0, h2781, h2885, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2902 | h2902
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2903 | h2903
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2904 | h2904
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2905 | h2905
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2906 | h2906
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2907 | h2907
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2908 | h2908
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2909 | h2909
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2910 | h2910
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2911 | h2911
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2912 | h2912
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2913 | h2913
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2914 | h2914
                              · linarith only [h2902, h2912, h2914, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases h0bigk with h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c | h2916c
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, hlam, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2080, hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2597, hlam, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2781, hlam, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, h2907, h2914, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, h2781, hc01, hlam, hphi, ht12, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2902, hlam, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, h2902, h2907, h2914, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, h2781, h2902, hc01, hlam, hphi, ht12, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2903, hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2905, hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h0, h2781, h2902, h2905, hc01, hlam, hphi, ht12, p2916_1, u2elo1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2781, hc01, hc15, hlam, hphi, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2904, hlam, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2906, hlam, p2916_0]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [h2907, hlam, p2916_1]
                                · have p2916_0 := h2916c.1
                                  have p2916_1 := h2916c.2.1
                                  have p2916_2 := h2916c.2.2.1
                                  have p2916_3 := h2916c.2.2.2
                                  linarith only [hlam, p2916_0]
                            · linarith only [h0, h2902, h2906, h2912, h2913, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2943 | h2943
                            · linarith only [h0, h2902, h2905, h2912, h2943, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2945 | h2945
                              · rcases h0bigk with h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c | h2946c
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h0, hlam, p2946_1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2080, hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2597, hlam, p2946_1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2781, hlam, p2946_1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h0, h2781, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2080, h2908, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2902, hlam, p2946_1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2080, h2781, h2907, h2908, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2080, h2781, h2908, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2597, h2908, h2909, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2903, hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2905, hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2597, h2906, h2908, h2909, h2943, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2781, h2908, h2909, h2911, hc01, hlam, hphi, ht12, p2946_1, u2elo1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2904, hlam, p2946_1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2906, hlam, p2946_0]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [h2907, hlam, p2946_1]
                                · have p2946_0 := h2946c.1
                                  have p2946_1 := h2946c.2.1
                                  have p2946_2 := h2946c.2.2.1
                                  have p2946_3 := h2946c.2.2.2
                                  linarith only [hlam, p2946_0]
                              · linarith only [h2597, h2907, h2908, h2909, h2912, h2945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2597, h2907, h2911, hlam]
                      · linarith only [h2080, h2906, h2910, hlam]
                    · linarith only [h2080, h2905, h2909, hlam]
                  · linarith only [h0, h2908, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2977 | h2977
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2978 | h2978
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2979 | h2979
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2980 | h2980
                        · linarith only [h2597, h2907, h2977, h2978, h2980, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2982 | h2982
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2983 | h2983
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2984 | h2984
                              · linarith only [h0, h2902, h2980, h2982, h2984, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases h0bigk with h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, hlam, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2080, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2597, hlam, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2781, hlam, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2597, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2781, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2080, h2977, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2902, hlam, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2080, h2597, h2977, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2080, h2781, h2977, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2903, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2905, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2907, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2781, h2977, h2979, hc01, hlam, hphi, ht12, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2904, hlam, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2906, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2781, h2977, h2979, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2986_1, u2elo1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                            · linarith only [h2080, h2906, h2977, h2982, h2983, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3013 | h3013
                            · linarith only [h2080, h2905, h2977, h2982, h3013, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3015 | h3015
                              · linarith only [h2080, h2597, h2905, h2977, h2980, h3015, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases h0bigk with h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h0, hlam, p3017_1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2080, hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2597, hlam, p3017_1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2781, hlam, p3017_1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h0, h2906, h2982, h3015, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h0, h2905, h2982, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2080, h2977, hc01, hlam, hphi, ht12, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2902, hlam, p3017_1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2080, h2905, h2977, h2982, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2080, h2781, h2977, hc01, hlam, hphi, ht12, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p3017_1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2903, hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2905, hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2907, hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2781, h2977, h2979, hc01, hlam, hphi, ht12, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2904, hlam, p3017_1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2906, hlam, p3017_0]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [h2781, h2977, h2979, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3017_1, u2elo1]
                                · have p3017_0 := h3017c.1
                                  have p3017_1 := h3017c.2.1
                                  have p3017_2 := h3017c.2.2.1
                                  have p3017_3 := h3017c.2.2.2
                                  linarith only [hlam, p3017_0]
                      · linarith only [h2080, h2906, h2979, hlam]
                    · linarith only [h0, h2080, h2903, h2905, h2978, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2977, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3046 | h3046
                · linarith only [h2905, h2906, h3046, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3048 | h3048
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3049 | h3049
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3050 | h3050
                      · linarith only [h2905, h2906, h3048, h3050, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3052 | h3052
                        · linarith only [h2597, h3046, h3048, h3049, h3052, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3054 | h3054
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3055 | h3055
                            · linarith only [h2902, h3050, h3055, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3057 | h3057
                              · linarith only [h2904, h3054, h3055, h3057, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases h0bigk with h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, hlam, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2080, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2597, hlam, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2781, hlam, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p3059_1, u2elo1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3059_1, u2elo1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, h2597, hc01, hlam, hphi, ht12, p3059_1, u2elo1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, h2902, h2906, h3054, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3059_1, u2elo1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2902, hlam, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2080, h2597, h3050, h3057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2906, hlam, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2903, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2905, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3046, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2781, hc01, hc15, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2904, hlam, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, h2904, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3059_1, u2elo1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h0, h2597, h2904, hc01, hlam, hphi, ht12, p3059_1, u2elo1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                          · linarith only [h2905, h2906, h3054, hc23, hc35, hlam, hphi]
                    · linarith only [h2080, h2905, h3049, hlam]
                  · linarith only [h0, h3048, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3088 | h3088
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3089 | h3089
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3090 | h3090
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3091 | h3091
                    · linarith only [h2905, h3088, h3090, h3091, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3093 | h3093
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3094 | h3094
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3095 | h3095
                          · linarith only [h2080, h3091, h3095, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3097 | h3097
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3098 | h3098
                              · rcases h0bigk with h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2080, hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2597, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2781, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, h2902, h3097, h3098, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, h2902, h2905, h3097, h3098, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2902, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2905, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, h2781, h2903, h2905, hc01, hlam, hphi, ht12, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, h2903, hc01, hlam, hphi, ht12, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2903, hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, h2903, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h0, h2781, h2903, hc01, hlam, hphi, ht12, p3099_1, u2elo1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2781, hc01, hc15, hlam, hphi, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h2904, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h3088, hlam, p3099_0]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [h3089, hlam, p3099_1]
                                · have p3099_0 := h3099c.1
                                  have p3099_1 := h3099c.2.1
                                  have p3099_2 := h3099c.2.2.1
                                  have p3099_3 := h3099c.2.2.2
                                  linarith only [hlam, p3099_0]
                              · linarith only [h2080, h3091, h3098, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h2080, h3088, h3091, h3097, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h2597, h2903, h3089, h3094, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h2080, h2903, h2905, h3088, h3093, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3090, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2905, h3088, h3089, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3131 | h3131
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3132 | h3132
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3133 | h3133
                    · linarith only [h2080, h2905, h3132, h3133, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3135 | h3135
                      · linarith only [h2080, h3088, h3132, h3135, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3137 | h3137
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3138 | h3138
                          · linarith only [h2080, h3133, h3138, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3140 | h3140
                            · linarith only [h2080, h3135, h3140, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3142 | h3142
                              · rcases h0bigk with h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [hlam, p3143_0]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2080, hlam, p3143_0]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2597, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2781, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [hlam, p3143_0]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, h2080, h3088, h3131, hc01, hlam, hphi, ht12, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, h2080, h3088, hc01, hlam, hphi, ht12, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2902, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [hlam, p3143_0]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2905, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h3088, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2903, hlam, p3143_0]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, h2903, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [hlam, p3143_0]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, h2080, h2903, h3088, hc01, hlam, hphi, ht12, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2781, h3137, hc01, hc14, hlam, hphi, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h2904, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h0, h2080, h2904, hc01, hlam, hphi, ht12, p3143_1, u2elo1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [h3131, hlam, p3143_1]
                                · have p3143_0 := h3143c.1
                                  have p3143_1 := h3143c.2.1
                                  have p3143_2 := h3143c.2.2.1
                                  have p3143_3 := h3143c.2.2.2
                                  linarith only [hlam, p3143_0]
                              · linarith only [h2597, h3131, h3133, h3142, hlam]
                        · linarith only [h2597, h3131, h3137, hlam]
                  · linarith only [h0, h3132, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3172 | h3172
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3173 | h3173
                    · linarith only [h2080, h2905, h3172, h3173, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3175 | h3175
                      · linarith only [h2080, h3088, h3173, h3175, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3177 | h3177
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3178 | h3178
                          · linarith only [h2902, h3173, h3178, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3180 | h3180
                            · linarith only [h2080, h3175, h3180, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3182 | h3182
                              · rcases h0bigk with h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2080, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2597, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2781, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p3183_1, u2elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3183_1, u2elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3183_1, u2elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p3183_1, u2elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2902, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2905, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h3088, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2597, h3173, hc01, hc34, hlam, hphi, ht12, ht23, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2903, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2903, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3183_1, u2elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h3131, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2781, hc01, hc15, hlam, hphi, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2904, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2080, h2904, hc01, hlam, hphi, ht12, p3183_1, u2elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h3131, h3173, h3177, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                              · linarith only [h3173, h3177, h3182, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3210 | h3210
                          · linarith only [h2902, h2905, h3210, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3212 | h3212
                            · linarith only [h2902, h3088, h3212, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3214 | h3214
                              · linarith only [h2080, h3173, h3177, h3214, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h2080, h3173, h3214, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h3172, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3218 | h3218
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3219 | h3219
              · linarith only [h2902, h2904, h3219, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3221 | h3221
                · linarith only [h2902, h2904, h3218, h3221, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3223 | h3223
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3224 | h3224
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3225 | h3225
                      · linarith only [h2080, h3219, h3223, h3225, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3227 | h3227
                        · linarith only [h2597, h3221, h3224, h3225, h3227, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3229 | h3229
                          · linarith only [h2902, h2904, h3229, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · linarith only [h2080, h3218, h3225, h3229, hc23, hc35, hlam, hphi]
                    · linarith only [h2080, h2902, h2904, h3218, h3224, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h3223, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3234 | h3234
              · linarith only [h2903, h2904, h3218, h3234, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3236 | h3236
                · linarith only [h2903, h2904, h3236, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3238 | h3238
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3239 | h3239
                    · linarith only [h2080, h3218, h3238, h3239, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3241 | h3241
                      · linarith only [h2080, h3234, h3238, h3241, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3243 | h3243
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3244 | h3244
                          · linarith only [h2902, h2904, h3236, h3239, h3243, h3244, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3246 | h3246
                            · linarith only [h2903, h2904, h3241, h3244, h3246, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3248 | h3248
                              · rcases h0bigk with h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h0, hlam, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2080, hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2597, hlam, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2781, hlam, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2904, hc01, hlam, hphi, ht12, p3249_1, u2elo4]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2080, h2904, hc01, hlam, hphi, ht12, p3249_1, u2elo4]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2080, h2904, h3218, hc01, hlam, hphi, ht12, p3249_1, u2elo4]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2904, hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h3218, h3236, h3243, hc01, hc14, hlam, hphi, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2902, hlam, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h3218, hlam, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h3234, hlam, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2903, h2904, h3236, h3239, h3243, h3244, hc01, hc23, hc34, hlam, hphi, ht12, p3249_1, u2elo4]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2903, hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h3236, h3239, h3243, hc03, hc34, hlam, hphi, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h3236, hlam, p3249_0]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2781, hc01, hc15, hlam, hphi, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2903, h2904, h3244, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3249_1, u2elo4]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h2080, h2904, hc01, hlam, hphi, ht12, p3249_1, u2elo4]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [h3236, h3239, h3243, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3249_1]
                                · have p3249_0 := h3249c.1
                                  have p3249_1 := h3249c.2.1
                                  have p3249_2 := h3249c.2.2.1
                                  have p3249_3 := h3249c.2.2.2
                                  linarith only [hlam, p3249_0]
                              · linarith only [h3239, h3243, h3248, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3276 | h3276
                          · linarith only [h2902, h2904, h3276, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3278 | h3278
                            · linarith only [h2903, h2904, h3276, h3278, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3280 | h3280
                              · linarith only [h2597, h2903, h2904, h3243, h3276, h3280, hc01, hc23, hc34, hlam, hphi, ht12, u2elo4]
                              · linarith only [h2080, h2903, h2904, h3239, h3276, h3280, hc01, hc23, hc45, hlam, hphi, ht12, ht34, u2elo4]
                  · linarith only [h0, h3238, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3284 | h3284
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3285 | h3285
            · linarith only [h2902, h2903, h3285, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3287 | h3287
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3288 | h3288
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3289 | h3289
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3290 | h3290
                    · linarith only [h3285, h3287, h3289, h3290, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3292 | h3292
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3293 | h3293
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3294 | h3294
                          · linarith only [h2902, h2903, h3290, h3294, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3296 | h3296
                            · linarith only [h2902, h2903, h3296, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                            · linarith only [h2080, h3287, h3290, h3296, hc23, hc34, hlam, hphi]
                        · linarith only [h2597, h3288, h3293, hlam]
                      · linarith only [h2080, h3287, h3292, hlam]
                  · linarith only [h0, h3289, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2902, h2903, h3287, h3288, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3303 | h3303
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3304 | h3304
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3305 | h3305
                    · linarith only [h2080, h3285, h3304, h3305, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3307 | h3307
                      · linarith only [h2080, h3287, h3304, h3307, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3309 | h3309
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3310 | h3310
                          · linarith only [h2902, h2903, h3305, h3310, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3312 | h3312
                            · linarith only [h2080, h2902, h2903, h3307, h3312, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3314 | h3314
                              · rcases h0bigk with h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [hlam, p3315_0]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h0, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2080, hlam, p3315_0]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2597, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2781, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2903, hc01, hlam, hphi, ht12, p3315_1, u2elo3]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [hlam, p3315_0]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2080, h2903, hc01, hlam, hphi, ht12, p3315_1, u2elo3]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2903, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2903, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p3315_1, u2elo3]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2902, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [hlam, p3315_0]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h3285, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h3287, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2903, h3284, h3312, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3315_1, u2elo3]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2903, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3315_1, u2elo3]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [hlam, p3315_0]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2080, h2903, h3287, hc01, hlam, hphi, ht12, p3315_1, u2elo3]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2781, hc01, hc15, hlam, hphi, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h3284, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h2080, h3284, hc01, hlam, hphi, ht12, p3315_1, u2elo0]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [h3303, hlam, p3315_1]
                                · have p3315_0 := h3315c.1
                                  have p3315_1 := h3315c.2.1
                                  have p3315_2 := h3315c.2.2.1
                                  have p3315_3 := h3315c.2.2.2
                                  linarith only [hlam, p3315_0]
                              · linarith only [h2597, h2903, h3284, h3303, h3305, h3314, hc01, hlam, hphi, ht12, u2elo3]
                        · linarith only [h2597, h3303, h3309, hlam]
                  · linarith only [h0, h3304, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2903, h3284, h3303, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3345 | h3345
            · linarith only [h2902, h2903, h3345, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3347 | h3347
              · linarith only [h2902, h3284, h3347, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3349 | h3349
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3350 | h3350
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3351 | h3351
                    · linarith only [h2080, h3345, h3350, h3351, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3353 | h3353
                      · linarith only [h2080, h3347, h3350, h3353, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3355 | h3355
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3356 | h3356
                          · linarith only [h2902, h2903, h3351, h3356, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3358 | h3358
                            · linarith only [h2080, h2902, h2903, h3353, h3358, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3360 | h3360
                              · rcases h0bigk with h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [hlam, p3361_0]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h0, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2080, hlam, p3361_0]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2597, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2781, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2903, hc01, hlam, hphi, ht12, p3361_1, u2elo3]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [hlam, p3361_0]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2080, h2903, hc01, hlam, hphi, ht12, p3361_1, u2elo3]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2903, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h3284, hlam, p3361_0]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2080, hc01, hc13, hlam, hphi, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2902, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [hlam, p3361_0]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h3345, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h3347, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2597, hc01, hc14, hlam, hphi, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2903, hc02, hlam, hphi, p3361_1, u2elo3]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2903, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3361_1, u2elo3]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [hlam, p3361_0]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2902, h2903, h3284, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3361_1, u2elo3]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2781, h3355, hc01, hc14, hlam, hphi, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2902, h3284, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3361_1, u2elo4]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h2080, h3284, hc01, hlam, hphi, ht12, p3361_1, u2elo4]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [h3349, hlam, p3361_1]
                                · have p3361_0 := h3361c.1
                                  have p3361_1 := h3361c.2.1
                                  have p3361_2 := h3361c.2.2.1
                                  have p3361_3 := h3361c.2.2.2
                                  linarith only [hlam, p3361_0]
                              · linarith only [h2597, h2903, h3349, h3351, h3360, hc01, hlam, hphi, ht12, u2elo3]
                        · linarith only [h2597, h3349, h3355, hlam]
                  · linarith only [h2902, h3350, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3390 | h3390
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3391 | h3391
                    · linarith only [h2080, h3345, h3390, h3391, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3393 | h3393
                      · linarith only [h2080, h3347, h3390, h3393, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3395 | h3395
                        · linarith only [h2902, h2903, h3349, h3391, h3395, hc23, hc34, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3397 | h3397
                          · linarith only [h2597, h2902, h2903, h3395, h3397, hc34, hc45, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3399 | h3399
                            · linarith only [h2902, h2903, h3399, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3401 | h3401
                              · linarith only [h2080, h3391, h3395, h3401, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h2080, h3391, h3401, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h2902, h2903, h3390, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3405 | h3405
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3406 | h3406
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3407 | h3407
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3408 | h3408
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3409 | h3409
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3410 | h3410
                  · linarith only [h2902, h3410, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h3410, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3413 | h3413
                  · linarith only [h2902, h3405, h3413, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h3413, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2902, h3406, h3408, hlam]
            · linarith only [h2902, h3405, h3407, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3418 | h3418
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3419 | h3419
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3420 | h3420
                · linarith only [h3405, h3406, h3420, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3422 | h3422
                  · linarith only [h2902, h3405, h3422, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h3422, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3425 | h3425
                · linarith only [h2902, h3405, h3419, h3425, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3427 | h3427
                  · linarith only [h2902, h3405, h3427, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h3427, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2902, h3405, h3418, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3431 | h3431
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3432 | h3432
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3433 | h3433
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3434 | h3434
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3435 | h3435
                  · linarith only [h2902, h3435, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h3435, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h3405, h3431, h3434, hlam]
              · linarith only [h2902, h3431, h3433, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3440 | h3440
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3441 | h3441
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3442 | h3442
                  · linarith only [h2781, h2902, h3431, h3442, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3442, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2902, h3431, h3432, h3441, hlam]
              · linarith only [h2902, h3431, h3440, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3447 | h3447
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3448 | h3448
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3449 | h3449
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3450 | h3450
                  · linarith only [h0, h2902, h3450, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3450, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3453 | h3453
                  · linarith only [h0, h2902, h3453, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3453, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3456 | h3456
                · linarith only [h3447, h3448, h3456, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3458 | h3458
                  · linarith only [h0, h2902, h3458, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3458, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3461 | h3461
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3462 | h3462
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3463 | h3463
                  · linarith only [h0, h2902, h3463, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3463, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h3447, h3461, h3462, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3467 | h3467
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3468 | h3468
                  · linarith only [h0, h2902, h3468, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3468, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3471 | h3471
                  · linarith only [h0, h2902, h3471, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3471, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2080 | h2080
  · exact r1l7_20_12_13_H_I_L_0_L_I_x1_x0 m hb0 hb2 hb3 h0 h2080
  · exact r1l7_20_12_13_H_I_L_0_L_I_x1_x1 m hb0 hb2 hb3 h0 h2080

end R2N4
