import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1662 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2282 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2613 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2614 | h2614
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2615 | h2615
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2616 | h2616
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2617 | h2617
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2618 | h2618
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2619 | h2619
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2620 | h2620
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2621 | h2621
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2622 | h2622
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2623 | h2623
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2624 | h2624
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2625 | h2625
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2626 | h2626
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2627 | h2627
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2628 | h2628
                              · rcases h0bigk with h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h0, hlam, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h1662, hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2282, hlam, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2282, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h0, h2614, h2625, h2628, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h0, h2282, h2613, h2622, h2626, h2628, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  rcases p2629_3 (m.d 0 1) (by simp) with h2639 | h2639
                                  · linarith only [h0, h2639, hlam]
                                  · linarith only [h2613, h2639, hlam]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2613, h2622, h2626, h2628, hc03, hc45, hlam, hphi, ht0b, ht5b, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2614, hlam, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h1662, h2282, h2613, h2622, h2626, h2628, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2629_1, u3elo1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h1662, h2613, h2622, h2626, h2628, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2629_1, u3elo1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2613, h2622, h2626, h2628, hc04, hc45, hlam, hphi, ht0b, ht5b, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2615, hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2617, hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h1662, h2613, h2617, h2622, h2626, h2628, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2629_1, u3elo1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2613, hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2616, hlam, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2618, hlam, p2629_0]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [h2619, hlam, p2629_1]
                                · have p2629_0 := h2629c.1
                                  have p2629_1 := h2629c.2.1
                                  have p2629_2 := h2629c.2.2.1
                                  have p2629_3 := h2629c.2.2.2
                                  linarith only [hlam, p2629_0]
                              · linarith only [h1662, h2613, h2624, h2628, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1662, h2613, h2624, h2627, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1662, h2618, h2625, h2626, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1662, h2617, h2625, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1662, h2282, h2617, h2619, h2624, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h2613, h2622, h2623, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                  · linarith only [h0, h2613, h2616, h2622, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2615, h2621, hlam]
              · linarith only [h0, h2613, h2620, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h2282, h2613, h2619, hlam]
          · linarith only [h1662, h2613, h2618, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2668 | h2668
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2669 | h2669
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2670 | h2670
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2671 | h2671
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2672 | h2672
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2673 | h2673
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2674 | h2674
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2675 | h2675
                        · linarith only [h1662, h2617, h2675, hc01, hlam, hphi, ht12, ht23, u3elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2677 | h2677
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2678 | h2678
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2679 | h2679
                              · rcases h0bigk with h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h0, hlam, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h1662, hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2282, hlam, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2282, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h0, h1662, h2613, h2672, h2677, h2679, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h0, h1662, h2613, h2617, h2672, h2677, h2679, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  rcases p2680_3 (m.d 0 1) (by simp) with h2690 | h2690
                                  · linarith only [h0, h2690, hlam]
                                  · linarith only [h2613, h2690, hlam]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2613, h2672, h2677, h2679, hc03, hc45, hlam, hphi, ht0b, ht5b, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2614, hlam, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2617, hlam, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2613, h2617, h2672, h2677, h2679, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2680_1, u3elo3]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2613, h2617, h2672, h2677, h2679, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2680_1, u3elo3]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2615, hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2617, hc03, hlam, hphi, p2680_1, u3elo3]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2613, h2617, h2672, h2677, h2679, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2680_1, u3elo3]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2613, hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2616, hlam, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2668, hlam, p2680_0]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [h2669, hlam, p2680_1]
                                · have p2680_0 := h2680c.1
                                  have p2680_1 := h2680c.2.1
                                  have p2680_2 := h2680c.2.2.1
                                  have p2680_3 := h2680c.2.2.2
                                  linarith only [hlam, p2680_0]
                              · linarith only [h1662, h2613, h2617, h2669, h2679, hc04, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1662, h2613, h2674, h2675, h2677, h2678, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2617, h2668, h2677, hc23, hlam, hphi, u3elo3]
                      · linarith only [h2282, h2669, h2674, hlam]
                    · linarith only [h1662, h2673, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2616, h2672, hlam]
                · linarith only [h0, h2615, h2671, hlam]
              · linarith only [h0, h2670, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2282, h2613, h2669, hlam]
          · linarith only [h1662, h2613, h2668, hlam]
      · linarith only [h0, h2613, h2616, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2719 | h2719
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2720 | h2720
        · linarith only [h2614, h2615, h2720, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2722 | h2722
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2723 | h2723
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2724 | h2724
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2725 | h2725
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2726 | h2726
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2727 | h2727
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2728 | h2728
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2729 | h2729
                        · linarith only [h1662, h2613, h2614, h2720, h2726, h2729, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h2614, h2615, h2729, hc23, hlam, hphi, u3elo3]
                      · linarith only [h2282, h2723, h2728, hlam]
                    · linarith only [h1662, h2613, h2726, h2727, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                  · linarith only [h2614, h2615, h2725, h2726, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2735 | h2735
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2736 | h2736
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2737 | h2737
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2738 | h2738
                        · linarith only [h1662, h2720, h2738, hc01, hlam, hphi, ht12, ht23, u3elo2]
                        · linarith only [h0, h2613, h2725, h2735, h2738, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h1662, h2613, h2723, h2724, h2725, h2735, h2737, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1662, h2613, h2735, h2736, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                  · linarith only [h1662, h2613, h2719, h2724, h2735, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h2613, h2724, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h2613, h2615, h2723, hlam]
          · linarith only [h1662, h2613, h2722, hlam]
      · linarith only [h1662, h2613, h2614, h2719, hc23, hlam, hphi, u3elo1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2748 | h2748
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2749 | h2749
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2750 | h2750
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2751 | h2751
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2752 | h2752
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2753 | h2753
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2754 | h2754
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2755 | h2755
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2756 | h2756
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2757 | h2757
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2758 | h2758
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2759 | h2759
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2760 | h2760
                            · linarith only [h2614, h2748, h2753, h2760, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h2614, h2748, h2752, h2753, h2760, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h2282, h2614, h2748, h2759, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h2282, h2614, h2748, h2758, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2282, h2613, h2752, h2755, h2757, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2614, h2748, h2753, h2756, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h2282, h2614, h2748, h2753, h2755, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h2614, h2748, h2753, h2754, hlam]
              · linarith only [h0, h2613, h2753, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h2282, h2613, h2752, hlam]
          · linarith only [h2282, h2613, h2614, h2748, h2751, hlam]
        · linarith only [h2614, h2748, h2750, hlam]
      · linarith only [h2282, h2613, h2748, h2749, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2774 | h2774
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2775 | h2775
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2776 | h2776
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2777 | h2777
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2778 | h2778
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2779 | h2779
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2780 | h2780
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2781 | h2781
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2782 | h2782
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2783 | h2783
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2784 | h2784
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2785 | h2785
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2786 | h2786
                              · rcases h0bigk with h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h0, hlam, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h1662, hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2282, hlam, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h0, h2748, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2748, hc01, hc24, hlam, hphi, ht12, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2614, hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2748, hlam, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2613, h2614, h2778, h2780, h2784, h2786, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2787_1, u3elo1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2613, h2780, h2784, h2786, hc03, hc45, hlam, hphi, ht0b, ht5b, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2614, h2778, hc02, hlam, hphi, ht23, p2787_1, u3elo1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2614, h2778, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2787_1, u3elo1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2613, h2614, h2778, h2780, h2784, h2786, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2787_1, u3elo1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2613, h2780, h2784, h2786, hc04, hc45, hlam, hphi, ht0b, ht5b, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h0, h2613, h2748, h2780, h2784, h2786, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2775, hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2613, h2614, h2775, h2778, h2780, h2784, h2786, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2787_1, u3elo1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2613, hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2774, hlam, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2776, hlam, p2787_0]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [h2777, hlam, p2787_1]
                                · have p2787_0 := h2787c.1
                                  have p2787_1 := h2787c.2.1
                                  have p2787_2 := h2787c.2.2.1
                                  have p2787_3 := h2787c.2.2.2
                                  linarith only [hlam, p2787_0]
                              · linarith only [h1662, h2613, h2782, h2786, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h0, h2613, h2748, h2782, h2785, hlam]
                          · linarith only [h0, h2748, h2783, h2784, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2613, h2614, h2782, h2783, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h1662, h2282, h2775, h2777, h2782, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2614, h2778, h2781, hc02, hlam, hphi, ht23, u3elo4]
                  · linarith only [h2614, h2774, h2780, hc12, hc23, hlam, hphi]
                · linarith only [h0, h2614, h2778, h2779, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2613, h2778, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h2282, h2613, h2777, hlam]
          · linarith only [h0, h2613, h2748, h2775, h2776, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2824 | h2824
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2825 | h2825
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2826 | h2826
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2827 | h2827
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2828 | h2828
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2829 | h2829
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2830 | h2830
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2831 | h2831
                        · linarith only [h2775, h2826, h2831, hc03, hlam, hphi, u3elo1]
                        · linarith only [h0, h2613, h2614, h2828, h2831, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h2613, h2748, h2825, h2827, h2828, h2830, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1662, h2613, h2828, h2829, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                  · linarith only [h0, h2614, h2826, h2828, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2613, h2614, h2826, h2827, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h2613, h2826, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h2282, h2613, h2825, hlam]
          · linarith only [h0, h2613, h2614, h2824, hlam]
      · linarith only [h0, h2613, h2774, hlam]

end R2N4
