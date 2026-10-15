import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1_x1_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1845 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2109 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2591 | h2591
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2592 | h2592
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2593 | h2593
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2594 | h2594
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2595 | h2595
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2596 | h2596
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2597 | h2597
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2598 | h2598
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2599 | h2599
                  · linarith only [h0, h2109, h2110, h2595, h2599, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h2109, h2110, h2594, h2595, h2599, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h2109, h2110, h2593, h2594, h2595, h2598, hc03, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h1845, h2109, h2596, h2597, hc24, hlam, hphi, u4elo3]
            · linarith only [h2110, h2595, h2596, hc03, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2605 | h2605
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2606 | h2606
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2607 | h2607
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2608 | h2608
                  · linarith only [h0, h2109, h2595, h2608, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h2594, h2605, h2608, hc24, hlam, hphi, u4elo0]
                · linarith only [h0, h2109, h2593, h2594, h2595, h2607, hc03, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h1845, h2109, h2605, h2606, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h2109, h2605, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2614 | h2614
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2615 | h2615
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2616 | h2616
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2617 | h2617
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2618 | h2618
                  · linarith only [h2594, h2618, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2620 | h2620
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2621 | h2621
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2622 | h2622
                        · linarith only [h0, h2109, h2110, h2614, h2615, h2618, h2622, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2624 | h2624
                          · linarith only [h2109, h2594, h2615, h2620, h2624, hlam]
                          · rcases h3bigk with h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h1845, hlam, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2110, hlam, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2630 | h2630
                              · rcases p2626_3 (m.d 1 3) (by simp) with h2631 | h2631
                                · rcases p2626_3 (m.d 2 3) (by simp) with h2632 | h2632
                                  · rcases p2626_3 (m.d 3 4) (by simp) with h2633 | h2633
                                    · linarith only [h2633, hlam, p2626_0]
                                    · rcases p2626_3 (m.d 3 5) (by simp) with h2635 | h2635
                                      · linarith only [h2593, h2635, hlam]
                                      · linarith only [h2624, h2635, hlam]
                                  · linarith only [h2620, h2632, hlam]
                                · linarith only [h2616, h2631, hlam]
                              · linarith only [h2630, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2641 | h2641
                              · rcases p2626_3 (m.d 1 3) (by simp) with h2642 | h2642
                                · rcases p2626_3 (m.d 2 3) (by simp) with h2643 | h2643
                                  · rcases p2626_3 (m.d 3 4) (by simp) with h2644 | h2644
                                    · linarith only [h2592, h2644, hlam]
                                    · rcases p2626_3 (m.d 3 5) (by simp) with h2646 | h2646
                                      · linarith only [h2646, hlam, p2626_0]
                                      · rcases h3emin with h2648 | h2648 | h2648 | h2648 | h2648
                                        · rcases h4bigk with h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2594, hc14, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2594, h2620, hc34, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2594, hc34, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2594, hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2109, hlam, p2649_1]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, h2620, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2649_1]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2649_1]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2618, hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2591, hlam, p2649_1]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2615, hlam, p2649_1]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2649_1, u4elo2]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2622, hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2592, hlam, p2649_1]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2616, hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2620, hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2624, hlam, p2649_0]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2615, hc24, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [h2620, hc34, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2649_1, u4elo4]
                                          · have p2649_0 := h2649c.1
                                            have p2649_1 := h2649c.2.1
                                            have p2649_2 := h2649c.2.2.1
                                            have p2649_3 := h2649c.2.2.2
                                            linarith only [hlam, p2649_0]
                                        · rcases h4bigk with h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2615, h2620, hc34, hlam, hphi, p2675_1, u4elo0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, h2620, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2594, hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2109, hlam, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2620, hc34, hlam, hphi, p2675_1, u4elo1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2618, hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2591, hlam, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2615, hlam, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2675_1, u4elo2]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2622, hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2592, hlam, p2675_1]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2616, hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2620, hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2624, hlam, p2675_0]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2675_1, u4elo4]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2675_1, u4elo4]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [h2620, hc34, hlam, hphi, p2675_1, u4elo4]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2675_1, u4elo4]
                                          · have p2675_0 := h2675c.1
                                            have p2675_1 := h2675c.2.1
                                            have p2675_2 := h2675c.2.2.1
                                            have p2675_3 := h2675c.2.2.2
                                            linarith only [hlam, p2675_0]
                                        · rcases h4bigk with h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2615, h2620, hc34, hlam, hphi, p2701_1, u4elo0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, h2620, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2594, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2109, hlam, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2620, hc34, hlam, hphi, p2701_1, u4elo1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2618, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2591, hlam, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2615, hlam, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2701_1, u4elo2]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2622, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2592, hlam, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2616, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2620, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2624, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2701_1, u4elo4]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2701_1, u4elo4]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2620, hc34, hlam, hphi, p2701_1, u4elo4]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2701_1, u4elo4]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                        · linarith only [h2624, h2648, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2626_1]
                                        · linarith only [h2648, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2626_1]
                                  · linarith only [h2621, h2643, hlam]
                                · linarith only [h2617, h2642, hlam]
                              · linarith only [h2641, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2732 | h2732
                              · linarith only [h1845, h2732, hlam]
                              · rcases p2626_3 (m.d 1 3) (by simp) with h2734 | h2734
                                · rcases p2626_3 (m.d 2 3) (by simp) with h2735 | h2735
                                  · linarith only [h2614, h2735, hlam]
                                  · linarith only [h2110, h2735, hlam]
                                · linarith only [h1845, h2734, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h0, h2110, h2614, hc01, hc12, hlam, hphi, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2741 | h2741
                              · linarith only [h1845, h2741, hlam]
                              · linarith only [h2592, h2741, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2744 | h2744
                              · linarith only [h1845, h2744, hlam]
                              · linarith only [h2593, h2744, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h0, h2109, h2110, h2614, h2615, h2620, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2614, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2750 | h2750
                              · linarith only [h2110, h2750, hlam]
                              · linarith only [h2592, h2750, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 3) (by simp) with h2753 | h2753
                              · linarith only [h2110, h2753, hlam]
                              · linarith only [h2593, h2753, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2592, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2616, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2620, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2624, hlam, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2593, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2617, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2621, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2110, h2593, h2614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                      · linarith only [h2110, h2593, h2621, hlam]
                    · linarith only [h1845, h2109, h2110, h2620, hc14, hlam, hphi, u4elo3]
                · linarith only [h0, h2109, h2110, h2593, h2614, h2615, h2617, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1845, h2109, h2615, h2616, hc24, hlam, hphi, u4elo3]
            · linarith only [h2110, h2614, h2615, hc03, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2771 | h2771
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2772 | h2772
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2773 | h2773
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2774 | h2774
                  · linarith only [h0, h2109, h2614, h2774, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2776 | h2776
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2777 | h2777
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2778 | h2778
                        · linarith only [h0, h2109, h2594, h2614, h2771, h2778, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2780 | h2780
                          · linarith only [h2109, h2594, h2771, h2776, h2780, hlam]
                          · rcases h3bigk with h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h1845, hlam, p2782_1]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2110, hlam, p2782_1]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2786 | h2786
                              · rcases p2782_3 (m.d 1 3) (by simp) with h2787 | h2787
                                · rcases p2782_3 (m.d 2 3) (by simp) with h2788 | h2788
                                  · rcases p2782_3 (m.d 3 4) (by simp) with h2789 | h2789
                                    · linarith only [h2789, hlam, p2782_0]
                                    · rcases p2782_3 (m.d 3 5) (by simp) with h2791 | h2791
                                      · linarith only [h2593, h2791, hlam]
                                      · linarith only [h2780, h2791, hlam]
                                  · linarith only [h2776, h2788, hlam]
                                · linarith only [h2772, h2787, hlam]
                              · linarith only [h2786, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2797 | h2797
                              · rcases p2782_3 (m.d 1 3) (by simp) with h2798 | h2798
                                · rcases p2782_3 (m.d 2 3) (by simp) with h2799 | h2799
                                  · rcases p2782_3 (m.d 3 4) (by simp) with h2800 | h2800
                                    · linarith only [h2592, h2800, hlam]
                                    · rcases p2782_3 (m.d 3 5) (by simp) with h2802 | h2802
                                      · linarith only [h2802, hlam, p2782_0]
                                      · rcases h3emin with h2804 | h2804 | h2804 | h2804 | h2804
                                        · rcases h4bigk with h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2594, h2771, h2776, hc34, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2594, h2776, hc34, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2594, hc34, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2594, hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2109, hlam, p2805_1]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2805_1, u4elo1]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h0, h2109, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2805_1]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2774, hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2591, hlam, p2805_1]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2771, hlam, p2805_1]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2805_1, u4elo2]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2778, hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2592, hlam, p2805_1]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2772, hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2776, hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2780, hlam, p2805_0]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2771, hc24, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2805_1, u4elo4]
                                          · have p2805_0 := h2805c.1
                                            have p2805_1 := h2805c.2.1
                                            have p2805_2 := h2805c.2.2.1
                                            have p2805_3 := h2805c.2.2.2
                                            linarith only [hlam, p2805_0]
                                        · rcases h4bigk with h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2771, h2776, hc34, hlam, hphi, p2831_1, u4elo0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h0, h2109, h2614, h2776, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h0, h2109, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2594, hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2109, hlam, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2831_1, u4elo1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h0, h2109, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2774, hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2591, hlam, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2771, hlam, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2831_1, u4elo2]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2778, hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2592, hlam, p2831_1]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2772, hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2776, hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2780, hlam, p2831_0]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2831_1, u4elo4]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2831_1, u4elo4]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2831_1, u4elo4]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2831_1, u4elo4]
                                          · have p2831_0 := h2831c.1
                                            have p2831_1 := h2831c.2.1
                                            have p2831_2 := h2831c.2.2.1
                                            have p2831_3 := h2831c.2.2.2
                                            linarith only [hlam, p2831_0]
                                        · rcases h4bigk with h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2594, h2771, h2776, hc34, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2594, h2776, hc34, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2594, hc34, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2594, hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2109, hlam, p2857_1]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2857_1, u4elo1]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h0, h2109, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2857_1]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2774, hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2591, hlam, p2857_1]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2771, hlam, p2857_1]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2857_1, u4elo2]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2778, hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2592, hlam, p2857_1]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2772, hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2776, hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2780, hlam, p2857_0]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2857_1, u4elo4]
                                          · have p2857_0 := h2857c.1
                                            have p2857_1 := h2857c.2.1
                                            have p2857_2 := h2857c.2.2.1
                                            have p2857_3 := h2857c.2.2.2
                                            linarith only [hlam, p2857_0]
                                        · linarith only [h2771, h2776, h2804, hlam, ht34, u4elo1]
                                        · linarith only [h1845, h2614, h2804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2782_1]
                                  · linarith only [h2777, h2799, hlam]
                                · linarith only [h2773, h2798, hlam]
                              · linarith only [h2797, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2888 | h2888
                              · linarith only [h1845, h2888, hlam]
                              · rcases p2782_3 (m.d 1 3) (by simp) with h2890 | h2890
                                · rcases p2782_3 (m.d 2 3) (by simp) with h2891 | h2891
                                  · rcases p2782_3 (m.d 3 4) (by simp) with h2892 | h2892
                                    · linarith only [h2772, h2892, hlam]
                                    · rcases p2782_3 (m.d 3 5) (by simp) with h2894 | h2894
                                      · linarith only [h2773, h2894, hlam]
                                      · rcases h3emin with h2896 | h2896 | h2896 | h2896 | h2896
                                        · linarith only [h2614, h2896, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2782_1]
                                        · rcases h4bigk with h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c | h2898c
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2594, hc14, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2594, h2776, hc34, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2594, hc34, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2594, hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2109, hlam, p2898_1]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, h2776, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2782_1, p2898_1]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2782_1, p2898_1]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2774, hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2591, hlam, p2898_1]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2771, hlam, p2898_1]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2898_1, u4elo2]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2778, hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2592, hlam, p2898_1]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2772, hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2776, hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2780, hlam, p2898_0]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2771, hc24, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2898_1, u4elo4]
                                          · have p2898_0 := h2898c.1
                                            have p2898_1 := h2898c.2.1
                                            have p2898_2 := h2898c.2.2.1
                                            have p2898_3 := h2898c.2.2.2
                                            linarith only [hlam, p2898_0]
                                        · rcases h4bigk with h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2771, h2776, hc34, hlam, hphi, p2924_1, u4elo0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, h2776, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2782_1, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2782_1, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2594, hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2109, hlam, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2924_1, u4elo1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h0, h2109, h2110, h2614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2782_1, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2774, hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2591, hlam, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2771, hlam, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2924_1, u4elo2]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2778, hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2592, hlam, p2924_1]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2772, hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2776, hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2780, hlam, p2924_0]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2924_1, u4elo4]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2924_1, u4elo4]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [h2776, hc34, hlam, hphi, p2924_1, u4elo4]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2924_1, u4elo4]
                                          · have p2924_0 := h2924c.1
                                            have p2924_1 := h2924c.2.1
                                            have p2924_2 := h2924c.2.2.1
                                            have p2924_3 := h2924c.2.2.2
                                            linarith only [hlam, p2924_0]
                                        · linarith only [h0, h2109, h2110, h2614, h2771, h2776, h2896, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2782_1]
                                        · linarith only [h2593, h2614, h2896, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2782_1]
                                  · linarith only [h2110, h2891, hlam]
                                · linarith only [h1845, h2890, hlam]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2614, hlam, p2782_1]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2956 | h2956
                              · linarith only [h1845, h2956, hlam]
                              · linarith only [h2592, h2956, hlam]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2959 | h2959
                              · linarith only [h1845, h2959, hlam]
                              · linarith only [h2593, h2959, hlam]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2962 | h2962
                              · linarith only [h2110, h2962, hlam]
                              · rcases p2782_3 (m.d 1 3) (by simp) with h2964 | h2964
                                · linarith only [h2614, h2964, hlam]
                                · linarith only [h1845, h2964, hlam]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h1845, hc01, hc23, hlam, hphi, ht12, p2782_1]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h0, h2109, h2614, h2771, h2776, hlam, p2782_2]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              rcases p2782_3 (m.d 0 3) (by simp) with h2970 | h2970
                              · linarith only [h2110, h2970, hlam]
                              · linarith only [h2593, h2970, hlam]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2592, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2772, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2776, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2780, hlam, p2782_1]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2593, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2773, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2777, hlam, p2782_0]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [h2593, h2594, hc34, hlam, hphi, p2782_1, u4elo4]
                            · have p2782_0 := h2782c.1
                              have p2782_1 := h2782c.2.1
                              have p2782_2 := h2782c.2.2.1
                              have p2782_3 := h2782c.2.2.2
                              linarith only [hlam, p2782_0]
                      · linarith only [h0, h2109, h2593, h2594, h2614, h2771, h2776, h2777, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h2614, h2776, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1845, h2593, h2773, hlam]
              · linarith only [h1845, h2109, h2771, h2772, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h2109, h2591, h2594, h2771, hc14, hlam, hphi, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2988 | h2988
        · linarith only [h0, h2109, h2110, h2593, h2988, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2990 | h2990
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2991 | h2991
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2992 | h2992
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2993 | h2993
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2994 | h2994
                  · linarith only [h0, h2109, h2110, h2593, h2988, h2993, h2994, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h2109, h2110, h2593, h2993, h2994, hc14, hlam, hphi, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2997 | h2997
                  · linarith only [h0, h2109, h2110, h2990, h2997, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h2109, h2110, h2990, h2993, h2997, hc14, hlam, hphi, u4elo4]
              · linarith only [h0, h2109, h2110, h2990, h2991, h2992, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h2109, h2110, h2990, h2991, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3002 | h3002
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3003 | h3003
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3004 | h3004
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3005 | h3005
                  · linarith only [h0, h2109, h2110, h2593, h3004, h3005, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h2109, h2110, h2593, h3004, h3005, hc14, hlam, hphi, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3008 | h3008
                  · linarith only [h0, h2109, h2990, h3004, h3008, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h0, h2109, h2990, h3002, h3004, h3008, hc24, hlam, hphi, u4elo4]
              · linarith only [h0, h2109, h2990, h3002, h3003, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h2109, h3002, hc14, hlam, hphi, u4elo2]
    · linarith only [h0, h2109, h2110, h2592, hc14, hlam, hphi, u4elo3]
  · linarith only [h0, h2109, h2591, hc14, hlam, hphi, u4elo2]

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1845 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2109 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2110 | h2110
  · exact r1l7_13_24_L_I_M_LI_x1_x1_x0_x0 m hb3 hb4 h0 h1845 h2109 h2110
  · exact r1l7_13_24_L_I_M_LI_x1_x1_x0_x1 m hb3 hb4 h0 h1845 h2109 h2110

end R2N4
