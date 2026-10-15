import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5

set_option maxHeartbeats 6324000 in
set_option maxHeartbeats 6324000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4 m hb0 hb2 hb3 h0 h1 h2 h3 h4
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2543 | h2543
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2544 | h2544
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2545 | h2545
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2546 | h2546
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2547 | h2547
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2548 | h2548
              · linarith only [h0, h2543, h2548, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2550 | h2550
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2551 | h2551
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2552 | h2552
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2553 | h2553
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2554 | h2554
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2555 | h2555
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2556 | h2556
                            · linarith only [h0, h2550, h2556, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h2543, h2547, h2554, h2556, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h2555, h4, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h2550, h2554, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h2546, h2553, hc13, hlam, hphi, u3elo0]
                    · linarith only [h2545, h2548, h2550, h2552, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h2544, h2550, h2551, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h2543, h2550, h4, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2565 | h2565
              · linarith only [h0, h2543, h2565, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2567 | h2567
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2568 | h2568
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2569 | h2569
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2570 | h2570
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2571 | h2571
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2572 | h2572
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2573 | h2573
                            · linarith only [h2, h2547, h2567, h2573, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2575 | h2575
                              · linarith only [h2, h2547, h2567, h2571, h2575, hlam]
                              · rcases h0bigk with h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  rcases p2577_3 (m.d 0 1) (by simp) with h2579 | h2579
                                  · rcases p2577_3 (m.d 0 2) (by simp) with h2580 | h2580
                                    · linarith only [h0, h2580, hlam]
                                    · rcases p2577_3 (m.d 0 3) (by simp) with h2582 | h2582
                                      · linarith only [h1, h2582, hlam]
                                      · linarith only [h2582, h4, hlam]
                                  · linarith only [h0, h2579, hlam]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  rcases p2577_3 (m.d 0 1) (by simp) with h2586 | h2586
                                  · rcases p2577_3 (m.d 0 2) (by simp) with h2587 | h2587
                                    · linarith only [h0, h2587, hlam]
                                    · rcases p2577_3 (m.d 0 3) (by simp) with h2589 | h2589
                                      · linarith only [h1, h2589, hlam]
                                      · rcases p2577_3 (m.d 0 4) (by simp) with h2591 | h2591
                                        · linarith only [h2, h2591, hlam]
                                        · rcases p2577_3 (m.d 0 5) (by simp) with h2593 | h2593
                                          · linarith only [h2593, h3, hlam]
                                          · rcases h0emin with h2595 | h2595 | h2595 | h2595 | h2595
                                            · rcases h2bigk with h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2568, h2571, h2573, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2596_1]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h4, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2571, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2596_1, u3elo2]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2571, h2573, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2596_1, u3elo2]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h0, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2565, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h0, h2571, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2596_1, u3elo2]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h0, h2571, h2573, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2596_1, u3elo2]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hc02, hlam, hphi, ht23, p2596_1, u3elo2]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hc12, hlam, hphi, ht23, p2596_1, u3elo2]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                rcases p2596_3 (m.d 0 2) (by simp) with h2610 | h2610
                                                · linarith only [h2610, h4, hlam]
                                                · linarith only [h2543, h2610, hlam]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                rcases p2596_3 (m.d 0 2) (by simp) with h2613 | h2613
                                                · linarith only [h2613, h4, hlam]
                                                · linarith only [h2544, h2613, hlam]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2543, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2567, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2571, hlam, p2596_1]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2573, hlam, p2596_1]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2544, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2568, hlam, p2596_0]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2572, hlam, p2596_1]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [h2565, h2568, h2571, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2596_1, u3elo1]
                                              · have p2596_0 := h2596c.1
                                                have p2596_1 := h2596c.2.1
                                                have p2596_2 := h2596c.2.2.1
                                                have p2596_3 := h2596c.2.2.2
                                                linarith only [hlam, p2596_0]
                                            · linarith only [h2595, h4, hlam, ht01, ht12, ht23, u3elo2]
                                            · linarith only [h2595, hc01, hlam, p2577_1]
                                            · linarith only [h2547, h2595, hc45, hlam, ht01, ht12, ht23, ht34]
                                            · linarith only [h2544, h2595, h4, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h1, h2586, hlam]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  rcases p2577_3 (m.d 0 1) (by simp) with h2631 | h2631
                                  · rcases p2577_3 (m.d 0 2) (by simp) with h2632 | h2632
                                    · linarith only [h0, h2632, hlam]
                                    · linarith only [h2543, h2632, hlam]
                                  · linarith only [h2, h2631, hlam]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  rcases p2577_3 (m.d 0 1) (by simp) with h2636 | h2636
                                  · rcases p2577_3 (m.d 0 2) (by simp) with h2637 | h2637
                                    · linarith only [h0, h2637, hlam]
                                    · linarith only [h2544, h2637, hlam]
                                  · linarith only [h2636, h3, hlam]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h0, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h4, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2577_1, u3elo2]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2577_1, u3elo2]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h1, hlam, p2577_1]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p2577_1, u3elo0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  rcases p2577_3 (m.d 0 1) (by simp) with h2649 | h2649
                                  · rcases p2577_3 (m.d 0 2) (by simp) with h2650 | h2650
                                    · linarith only [h2650, h4, hlam]
                                    · linarith only [h2543, h2650, hlam]
                                  · linarith only [h2, h2649, hlam]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  rcases p2577_3 (m.d 0 1) (by simp) with h2654 | h2654
                                  · rcases p2577_3 (m.d 0 2) (by simp) with h2655 | h2655
                                    · linarith only [h2655, h4, hlam]
                                    · linarith only [h2544, h2655, hlam]
                                  · linarith only [h2654, h3, hlam]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2543, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2545, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2547, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h3, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2544, hlam, p2577_1]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2546, hlam, p2577_0]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [h2, h2544, h2567, h2571, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2577_1, u3elo2]
                                · have p2577_0 := h2577c.1
                                  have p2577_1 := h2577c.2.1
                                  have p2577_2 := h2577c.2.2.1
                                  have p2577_3 := h2577c.2.2.2
                                  linarith only [hlam, p2577_0]
                          · linarith only [h2572, h4, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2571, h4, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2546, h2570, hc13, hlam, hphi, u3elo0]
                    · linarith only [h2545, h2565, h2569, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h2544, h2567, h2568, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h2543, h2567, h4, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h2544, h2546, h4, hlam]
        · linarith only [h2543, h2545, h4, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2677 | h2677
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2678 | h2678
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2679 | h2679
            · linarith only [h2543, h2544, h2679, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2681 | h2681
              · linarith only [h0, h2681, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2683 | h2683
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2684 | h2684
                  · linarith only [h0, h2544, h2684, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2686 | h2686
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2687 | h2687
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2688 | h2688
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2689 | h2689
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2690 | h2690
                            · linarith only [h0, h2544, h2679, h2683, h2689, h2690, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2692 | h2692
                              · linarith only [h0, h2544, h2683, h2688, h2690, h2692, hlam]
                              · rcases h0bigk with h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  rcases p2694_3 (m.d 0 1) (by simp) with h2696 | h2696
                                  · rcases p2694_3 (m.d 0 2) (by simp) with h2697 | h2697
                                    · linarith only [h0, h2697, hlam]
                                    · rcases p2694_3 (m.d 0 3) (by simp) with h2699 | h2699
                                      · linarith only [h1, h2699, hlam]
                                      · linarith only [h2699, h4, hlam]
                                  · linarith only [h0, h2696, hlam]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  rcases p2694_3 (m.d 0 1) (by simp) with h2703 | h2703
                                  · rcases p2694_3 (m.d 0 2) (by simp) with h2704 | h2704
                                    · linarith only [h0, h2704, hlam]
                                    · rcases p2694_3 (m.d 0 3) (by simp) with h2706 | h2706
                                      · linarith only [h1, h2706, hlam]
                                      · rcases p2694_3 (m.d 0 4) (by simp) with h2708 | h2708
                                        · linarith only [h2, h2708, hlam]
                                        · rcases p2694_3 (m.d 0 5) (by simp) with h2710 | h2710
                                          · linarith only [h2710, h3, hlam]
                                          · rcases h0emin with h2712 | h2712 | h2712 | h2712 | h2712
                                            · rcases h2bigk with h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c | h2713c
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2544, h2689, hc12, hlam, hphi, ht23, p2713_1, u3elo2]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h4, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2544, h2688, h2689, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2713_1, u3elo2]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2544, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h0, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2681, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h0, h2544, h2688, h2689, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2713_1, u3elo2]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2684, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hc02, hlam, hphi, ht23, p2713_1, u3elo2]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hc12, hlam, hphi, ht23, p2713_1, u3elo2]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                rcases p2713_3 (m.d 0 2) (by simp) with h2727 | h2727
                                                · linarith only [h2727, h4, hlam]
                                                · linarith only [h2543, h2727, hlam]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h0, h2544, h2683, h2688, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2713_1, u3elo2]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2543, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2683, hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2688, hlam, p2713_1]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hlam, p2713_0]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2690, hlam, p2713_1]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h0, h2683, h2688, h2690, hc34, hc45, hlam, hphi, p2713_1]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2683, h2688, h2690, hc34, hc45, hlam, hphi, p2713_1]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [h2689, hlam, p2713_1]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                rcases p2713_3 (m.d 0 2) (by simp) with h2739 | h2739
                                                · linarith only [h2544, h2739, hlam]
                                                · linarith only [h2543, h2739, hlam]
                                              · have p2713_0 := h2713c.1
                                                have p2713_1 := h2713c.2.1
                                                have p2713_2 := h2713c.2.2.1
                                                have p2713_3 := h2713c.2.2.2
                                                linarith only [hlam, p2713_0]
                                            · linarith only [h2544, h2678, h2712, hlam, ht01, ht12, ht23, u3elo0]
                                            · linarith only [h2712, hlam, ht01, ht12, ht23, u3elo0]
                                            · linarith only [h2543, h2712, h4, hlam, ht01, ht12, ht23, u3elo2]
                                            · linarith only [h2678, h2712, hc01, hlam, p2694_1]
                                  · linarith only [h1, h2703, hlam]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  rcases p2694_3 (m.d 0 1) (by simp) with h2748 | h2748
                                  · rcases p2694_3 (m.d 0 2) (by simp) with h2749 | h2749
                                    · linarith only [h0, h2749, hlam]
                                    · linarith only [h2543, h2749, hlam]
                                  · linarith only [h2, h2748, hlam]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  rcases p2694_3 (m.d 0 1) (by simp) with h2753 | h2753
                                  · rcases p2694_3 (m.d 0 2) (by simp) with h2754 | h2754
                                    · linarith only [h0, h2754, hlam]
                                    · rcases p2694_3 (m.d 0 3) (by simp) with h2756 | h2756
                                      · linarith only [h1, h2756, hlam]
                                      · linarith only [h2678, h2756, hlam]
                                  · linarith only [h2753, h3, hlam]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h0, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h4, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2544, h2689, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2694_1, u3elo2]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2544, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h1, hlam, p2694_1]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p2694_1, u3elo0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  rcases p2694_3 (m.d 0 1) (by simp) with h2768 | h2768
                                  · rcases p2694_3 (m.d 0 2) (by simp) with h2769 | h2769
                                    · linarith only [h2769, h4, hlam]
                                    · linarith only [h2543, h2769, hlam]
                                  · linarith only [h2, h2768, hlam]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2683, h2684, h2688, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2694_1, u3elo2]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2543, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2677, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2679, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h3, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h0, h2544, h2683, h2688, h2689, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2694_1, u3elo2]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [h2678, hlam, p2694_0]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  rcases p2694_3 (m.d 0 1) (by simp) with h2782 | h2782
                                  · rcases p2694_3 (m.d 0 2) (by simp) with h2783 | h2783
                                    · linarith only [h2544, h2783, hlam]
                                    · linarith only [h2543, h2783, hlam]
                                  · linarith only [h2, h2782, hlam]
                                · have p2694_0 := h2694c.1
                                  have p2694_1 := h2694c.2.1
                                  have p2694_2 := h2694c.2.2.1
                                  have p2694_3 := h2694c.2.2.2
                                  linarith only [hlam, p2694_0]
                          · linarith only [h0, h2683, h2688, h2689, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h2683, h2688, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h2678, h2687, hc13, hlam, hphi, u3elo0]
                    · linarith only [h2677, h2681, h2683, h2686, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h2543, h2683, h4, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2793 | h2793
            · linarith only [h2543, h2678, h2793, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2795 | h2795
              · linarith only [h0, h2678, h2795, h4, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2797 | h2797
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2798 | h2798
                  · linarith only [h2544, h2795, h2798, hc02, hlam, hphi, ht23, u3elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2800 | h2800
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2801 | h2801
                      · linarith only [h1, h2678, h2801, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2803 | h2803
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2804 | h2804
                          · linarith only [h2678, h2804, hc03, hlam, hphi, u3elo2]
                          · linarith only [h0, h2797, h2803, h2804, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h2797, h2803, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h2677, h2800, hc13, hlam, hphi, u3elo0]
                · linarith only [h2543, h2678, h2797, h4, hc12, hlam, hphi, ht23, u3elo4]
        · linarith only [h2543, h2677, h4, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2811 | h2811
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2812 | h2812
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2813 | h2813
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2814 | h2814
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2815 | h2815
              · linarith only [h0, h2815, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2817 | h2817
                · linarith only [h2543, h2815, h2817, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2819 | h2819
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2820 | h2820
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2821 | h2821
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2822 | h2822
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2823 | h2823
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2824 | h2824
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2825 | h2825
                              · rcases h0bigk with h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c | h2826c
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  rcases p2826_3 (m.d 0 1) (by simp) with h2828 | h2828
                                  · rcases p2826_3 (m.d 0 2) (by simp) with h2829 | h2829
                                    · linarith only [h0, h2829, hlam]
                                    · rcases p2826_3 (m.d 0 3) (by simp) with h2831 | h2831
                                      · linarith only [h1, h2831, hlam]
                                      · linarith only [h2831, h4, hlam]
                                  · linarith only [h0, h2828, hlam]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h1, h2820, h2825, hc01, hc45, hlam, hphi, ht0b, ht5b, p2826_1]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  rcases p2826_3 (m.d 0 1) (by simp) with h2836 | h2836
                                  · rcases p2826_3 (m.d 0 2) (by simp) with h2837 | h2837
                                    · linarith only [h0, h2837, hlam]
                                    · rcases p2826_3 (m.d 0 3) (by simp) with h2839 | h2839
                                      · linarith only [h1, h2839, hlam]
                                      · linarith only [h2812, h2839, hlam]
                                  · linarith only [h2, h2836, hlam]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  rcases p2826_3 (m.d 0 1) (by simp) with h2843 | h2843
                                  · rcases p2826_3 (m.d 0 2) (by simp) with h2844 | h2844
                                    · linarith only [h0, h2844, hlam]
                                    · linarith only [h2811, h2844, hlam]
                                  · linarith only [h2843, h3, hlam]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h0, hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h4, hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2543, hlam, p2826_1]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2543, h2822, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2826_1, u3elo2]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h1, hlam, p2826_1]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h4, hc02, hlam, hphi, ht23, p2826_1, u3elo2]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h0, h2543, h2819, h2823, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2826_1, u3elo2]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  rcases p2826_3 (m.d 0 1) (by simp) with h2857 | h2857
                                  · rcases p2826_3 (m.d 0 2) (by simp) with h2858 | h2858
                                    · linarith only [h2858, h4, hlam]
                                    · linarith only [h2811, h2858, hlam]
                                  · linarith only [h2857, h3, hlam]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2, hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h0, h2543, h2819, h2822, h2823, h2825, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2826_1, u3elo2]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2812, hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  rcases p2826_3 (m.d 0 1) (by simp) with h2866 | h2866
                                  · rcases p2826_3 (m.d 0 2) (by simp) with h2867 | h2867
                                    · linarith only [h2543, h2867, hlam]
                                    · linarith only [h2811, h2867, hlam]
                                  · linarith only [h2866, h3, hlam]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h3, hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2811, hlam, p2826_1]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2813, hlam, p2826_0]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [h2814, hlam, p2826_1]
                                · have p2826_0 := h2826c.1
                                  have p2826_1 := h2826c.2.1
                                  have p2826_2 := h2826c.2.2.1
                                  have p2826_3 := h2826c.2.2.2
                                  linarith only [hlam, p2826_0]
                              · linarith only [h0, h2543, h2819, h2822, h2824, h2825, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h0, h2543, h2814, h2819, h2824, hc04, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h2543, h2819, h2822, h2823, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h0, h2819, h2822, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h2813, h2820, h2821, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h2812, h2815, h2819, h2820, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h2811, h2819, h4, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h2543, h2811, h2814, hlam]
          · linarith only [h2543, h2811, h2812, h2813, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2885 | h2885
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2886 | h2886
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2887 | h2887
              · linarith only [h0, h2887, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2889 | h2889
                · linarith only [h2543, h2887, h2889, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2891 | h2891
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2892 | h2892
                    · linarith only [h1, h2812, h2892, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2894 | h2894
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2895 | h2895
                        · linarith only [h0, h2812, h2891, h2895, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h0, h2891, h2895, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h2885, h2894, hc13, hlam, hphi, u3elo0]
                  · linarith only [h2811, h2812, h2891, h4, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h2811, h2812, h2886, h4, hlam]
          · linarith only [h2811, h2885, h4, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2902 | h2902
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2903 | h2903
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2904 | h2904
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2905 | h2905
              · linarith only [h0, h2905, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2907 | h2907
                · linarith only [h2543, h2905, h2907, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2909 | h2909
                  · linarith only [h0, h2811, h2909, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2911 | h2911
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2912 | h2912
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2913 | h2913
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2914 | h2914
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2915 | h2915
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2916 | h2916
                              · rcases h0bigk with h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  rcases p2917_3 (m.d 0 1) (by simp) with h2919 | h2919
                                  · rcases p2917_3 (m.d 0 2) (by simp) with h2920 | h2920
                                    · linarith only [h0, h2920, hlam]
                                    · rcases p2917_3 (m.d 0 3) (by simp) with h2922 | h2922
                                      · linarith only [h1, h2922, hlam]
                                      · linarith only [h2922, h4, hlam]
                                  · linarith only [h0, h2919, hlam]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h1, h2911, h2916, hc01, hc45, hlam, hphi, ht0b, ht5b, p2917_1]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  rcases p2917_3 (m.d 0 1) (by simp) with h2927 | h2927
                                  · rcases p2917_3 (m.d 0 2) (by simp) with h2928 | h2928
                                    · linarith only [h0, h2928, hlam]
                                    · rcases p2917_3 (m.d 0 3) (by simp) with h2930 | h2930
                                      · linarith only [h1, h2930, hlam]
                                      · linarith only [h2902, h2930, hlam]
                                  · linarith only [h2, h2927, hlam]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  rcases p2917_3 (m.d 0 1) (by simp) with h2934 | h2934
                                  · rcases p2917_3 (m.d 0 2) (by simp) with h2935 | h2935
                                    · linarith only [h0, h2935, hlam]
                                    · rcases p2917_3 (m.d 0 3) (by simp) with h2937 | h2937
                                      · linarith only [h1, h2937, hlam]
                                      · linarith only [h2903, h2937, hlam]
                                  · linarith only [h2934, h3, hlam]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h0, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h4, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2543, hlam, p2917_1]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2811, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h1, hlam, p2917_1]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h0, h4, hc12, hlam, hphi, ht23, p2917_1, u3elo2]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2, h2911, h2916, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2917_1, u3elo2]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h0, h2811, h4, hc12, hlam, hphi, ht23, p2917_1, u3elo2]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h0, h2902, h4, hc12, hlam, hphi, ht23, p2917_1, u3elo2]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2902, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h0, h2811, h2902, h4, hc12, hlam, hphi, ht23, p2917_1, u3elo2]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h3, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h0, h2903, h4, hc12, hlam, hphi, ht23, p2917_1, u3elo2]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2903, hlam, p2917_0]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [h2904, hlam, p2917_1]
                                · have p2917_0 := h2917c.1
                                  have p2917_1 := h2917c.2.1
                                  have p2917_2 := h2917c.2.2.1
                                  have p2917_3 := h2917c.2.2.2
                                  linarith only [hlam, p2917_0]
                              · rcases h0bigk with h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  rcases p2961_3 (m.d 0 1) (by simp) with h2963 | h2963
                                  · rcases p2961_3 (m.d 0 2) (by simp) with h2964 | h2964
                                    · linarith only [h0, h2964, hlam]
                                    · rcases p2961_3 (m.d 0 3) (by simp) with h2966 | h2966
                                      · linarith only [h1, h2966, hlam]
                                      · linarith only [h2966, h4, hlam]
                                  · linarith only [h0, h2963, hlam]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2902, h2904, h2916, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2904, h2916, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  rcases p2961_3 (m.d 0 1) (by simp) with h2972 | h2972
                                  · rcases p2961_3 (m.d 0 2) (by simp) with h2973 | h2973
                                    · linarith only [h0, h2973, hlam]
                                    · rcases p2961_3 (m.d 0 3) (by simp) with h2975 | h2975
                                      · linarith only [h1, h2975, hlam]
                                      · linarith only [h2903, h2975, hlam]
                                  · linarith only [h2972, h3, hlam]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h0, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h4, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2543, hlam, p2961_1]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2811, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h1, hlam, p2961_1]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h4, hc02, hlam, hphi, ht23, p2961_1, u3elo2]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2904, h2916, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2961_1, u3elo2]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2909, h3, h4, hc12, hlam, hphi, ht23, p2961_1, u3elo2]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h0, h2902, h4, hc12, hlam, hphi, ht23, p2961_1, u3elo2]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2902, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2902, h2909, h3, h4, hc12, hlam, hphi, ht23, p2961_1, u3elo2]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h3, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h0, h2903, h4, hc12, hlam, hphi, ht23, p2961_1, u3elo2]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2903, hlam, p2961_0]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [h2904, hlam, p2961_1]
                                · have p2961_0 := h2961c.1
                                  have p2961_1 := h2961c.2.1
                                  have p2961_2 := h2961c.2.2.1
                                  have p2961_3 := h2961c.2.2.2
                                  linarith only [hlam, p2961_0]
                            · linarith only [h2543, h2904, h2915, hlam]
                          · linarith only [h0, h2914, h4, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h2913, h4, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2903, h2911, h2912, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h2902, h2905, h2911, h4, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3004 | h3004
              · linarith only [h0, h3004, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3006 | h3006
                · linarith only [h2543, h3004, h3006, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3008 | h3008
                  · linarith only [h0, h2811, h3008, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3010 | h3010
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3011 | h3011
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3012 | h3012
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3013 | h3013
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3014 | h3014
                            · linarith only [h0, h2543, h2904, h3012, h3014, hc12, hlam, hphi, ht23, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3016 | h3016
                              · linarith only [h1, h3010, h3014, h3016, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases h0bigk with h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c | h3018c
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  rcases p3018_3 (m.d 0 1) (by simp) with h3020 | h3020
                                  · rcases p3018_3 (m.d 0 2) (by simp) with h3021 | h3021
                                    · linarith only [h0, h3021, hlam]
                                    · rcases p3018_3 (m.d 0 3) (by simp) with h3023 | h3023
                                      · linarith only [h1, h3023, hlam]
                                      · linarith only [h3023, h4, hlam]
                                  · linarith only [h0, h3020, hlam]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  rcases p3018_3 (m.d 0 1) (by simp) with h3027 | h3027
                                  · rcases p3018_3 (m.d 0 2) (by simp) with h3028 | h3028
                                    · linarith only [h0, h3028, hlam]
                                    · rcases p3018_3 (m.d 0 3) (by simp) with h3030 | h3030
                                      · linarith only [h1, h3030, hlam]
                                      · rcases p3018_3 (m.d 0 4) (by simp) with h3032 | h3032
                                        · linarith only [h2, h3032, hlam]
                                        · rcases p3018_3 (m.d 0 5) (by simp) with h3034 | h3034
                                          · linarith only [h3, h3034, hlam]
                                          · rcases h0emin with h3036 | h3036 | h3036 | h3036 | h3036
                                            · rcases h2bigk with h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h2543, hc12, hc24, hlam, hphi, p3037_1]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h4, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h2543, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h2811, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h0, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3004, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3006, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3008, hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hc02, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hc12, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h0, h2543, hc12, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h0, h2543, h3014, hc12, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h0, h3014, hc12, hc45, hlam, hphi, ht23, ht34, p3037_1]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3014, hc12, hc45, hlam, hphi, ht23, ht34, p3037_1]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3012, hlam, p3037_1]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hlam, p3037_0]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3014, hlam, p3037_1]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h0, h3013, hc12, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3013, hc12, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h3013, hlam, p3037_1]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [h0, h2543, h3013, hc12, hlam, hphi, ht23, p3037_1, u3elo2]
                                              · have p3037_0 := h3037c.1
                                                have p3037_1 := h3037c.2.1
                                                have p3037_2 := h3037c.2.2.1
                                                have p3037_3 := h3037c.2.2.2
                                                linarith only [hlam, p3037_0]
                                            · linarith only [h3036, h4, hlam, ht01, ht12, ht23, u3elo2]
                                            · linarith only [h3036, hc01, hlam, p3018_1]
                                            · linarith only [h2811, h2904, h3013, h3036, hlam, ht01, ht12, ht23, u3elo2]
                                            · linarith only [h2811, h3013, h3036, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h1, h3027, hlam]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  rcases p3018_3 (m.d 0 1) (by simp) with h3068 | h3068
                                  · rcases p3018_3 (m.d 0 2) (by simp) with h3069 | h3069
                                    · linarith only [h0, h3069, hlam]
                                    · rcases p3018_3 (m.d 0 3) (by simp) with h3071 | h3071
                                      · linarith only [h1, h3071, hlam]
                                      · linarith only [h2902, h3071, hlam]
                                  · linarith only [h2, h3068, hlam]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  rcases p3018_3 (m.d 0 1) (by simp) with h3075 | h3075
                                  · rcases p3018_3 (m.d 0 2) (by simp) with h3076 | h3076
                                    · linarith only [h0, h3076, hlam]
                                    · rcases p3018_3 (m.d 0 3) (by simp) with h3078 | h3078
                                      · linarith only [h1, h3078, hlam]
                                      · linarith only [h2903, h3078, hlam]
                                  · linarith only [h3, h3075, hlam]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h4, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h2543, hlam, p3018_1]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h2811, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h1, hlam, p3018_1]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, p3018_1, u3elo0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, h2543, h4, hc12, hlam, hphi, ht23, p3018_1, u3elo2]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, h2811, h4, hc12, hlam, hphi, ht23, p3018_1, u3elo2]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h2, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, h2902, h4, hc12, hlam, hphi, ht23, p3018_1, u3elo2]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h2902, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h2904, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h3, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, h2811, h3013, hc12, hlam, hphi, ht23, p3018_1, u3elo2]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h2903, hlam, p3018_0]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [h0, h2543, h2811, h3013, hc12, hlam, hphi, ht23, p3018_1, u3elo2]
                                · have p3018_0 := h3018c.1
                                  have p3018_1 := h3018c.2.1
                                  have p3018_2 := h3018c.2.2.1
                                  have p3018_3 := h3018c.2.2.2
                                  linarith only [hlam, p3018_0]
                          · linarith only [h1, h3011, h3013, h4, hlam]
                        · linarith only [h0, h3012, h4, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2903, h3011, h4, hc13, hlam, hphi, u3elo2]
                    · linarith only [h2902, h3004, h3010, h4, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3106 | h3106
            · linarith only [h2902, h2903, h3106, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3108 | h3108
              · linarith only [h0, h3108, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3110 | h3110
                · linarith only [h2543, h3108, h3110, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3112 | h3112
                  · linarith only [h0, h2811, h3112, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3114 | h3114
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3115 | h3115
                      · linarith only [h1, h2903, h3115, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3117 | h3117
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3118 | h3118
                          · linarith only [h1, h2903, h3114, h3118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h0, h3118, h4, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h3117, h4, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h2902, h2903, h3114, hc13, hlam, hphi, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3123 | h3123
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3124 | h3124
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3125 | h3125
              · linarith only [h0, h2811, h2902, h3123, h3125, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3127 | h3127
                · linarith only [h2543, h3125, h3127, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3129 | h3129
                  · linarith only [h0, h2811, h3129, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3131 | h3131
                    · linarith only [h1, h2902, h3131, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3133 | h3133
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3134 | h3134
                        · linarith only [h2811, h2902, h3123, h3134, hc02, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h3134, h4, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2902, h3123, h3133, hc13, hlam, hphi, u3elo3]
            · linarith only [h2902, h3123, h3124, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3139 | h3139
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3140 | h3140
              · linarith only [h0, h3140, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3142 | h3142
                · linarith only [h2543, h3140, h3142, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3144 | h3144
                  · linarith only [h0, h2811, h3144, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3146 | h3146
                    · linarith only [h1, h2902, h3146, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3148 | h3148
                      · linarith only [h1, h3123, h3148, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3150 | h3150
                        · linarith only [h0, h2902, h3150, h4, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h3150, h4, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3153 | h3153
              · linarith only [h0, h3153, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3155 | h3155
                · linarith only [h0, h2543, h3155, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3157 | h3157
                  · linarith only [h0, h2811, h3157, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3159 | h3159
                    · linarith only [h1, h2902, h3159, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3161 | h3161
                      · linarith only [h1, h3123, h3161, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3163 | h3163
                        · linarith only [h2902, h3163, hc03, hlam, hphi, u3elo2]
                        · linarith only [h0, h3163, h4, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6492000 in
set_option maxHeartbeats 6492000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s3 m hb0 hb2 hb3 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3166 | h3166
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3167 | h3167
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3168 | h3168
        · linarith only [h0, h3, h3168, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3170 | h3170
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3171 | h3171
            · linarith only [h1, h3, h3171, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3173 | h3173
              · linarith only [h0, h3, h3166, h3170, h3173, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3175 | h3175
                · linarith only [h0, h3, h3171, h3175, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h3, h3166, h3171, h3175, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3178 | h3178
            · linarith only [h1, h3, h3170, h3178, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3180 | h3180
              · linarith only [h0, h3, h3167, h3180, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3182 | h3182
                · linarith only [h0, h3, h3178, h3182, hc23, hlam, hphi, u3elo4]
                · linarith only [h3166, h3168, h3182, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3185 | h3185
        · linarith only [h2, h3, h3167, h3185, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3187 | h3187
          · linarith only [h3166, h3167, h3187, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3189 | h3189
            · linarith only [h1, h3, h3187, h3189, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3191 | h3191
              · linarith only [h2, h3, h3191, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3193 | h3193
                · linarith only [h0, h3, h3189, h3193, hc23, hlam, hphi, u3elo4]
                · linarith only [h3166, h3167, h3193, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3196 | h3196
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3197 | h3197
        · linarith only [h0, h3, h3197, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3199 | h3199
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3200 | h3200
            · linarith only [h1, h3, h3200, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3202 | h3202
              · linarith only [h0, h3, h3166, h3196, h3200, h3202, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3204 | h3204
                · linarith only [h0, h3166, h3200, h3204, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3206 | h3206
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3207 | h3207
                    · linarith only [h1, h3, h3197, h3204, h3207, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3209 | h3209
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3210 | h3210
                        · linarith only [h1, h3, h3200, h3210, hlam]
                        · linarith only [h1, h3, h3204, h3210, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h3199, h3200, h3204, h3206, h3209, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h3166, h3196, h3200, h3206, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h3166, h3196, h3199, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3216 | h3216
        · linarith only [h1, h3, h3166, h3216, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3218 | h3218
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3219 | h3219
            · linarith only [h1, h3, h3219, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3221 | h3221
              · linarith only [h0, h3, h3218, h3219, h3221, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3223 | h3223
                · linarith only [h0, h3196, h3218, h3219, h3223, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3225 | h3225
                  · linarith only [h0, h3196, h3225, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3227 | h3227
                    · linarith only [h1, h3, h3216, h3223, h3227, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3229 | h3229
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3230 | h3230
                        · linarith only [h1, h3, h3219, h3230, hlam]
                        · linarith only [h1, h3, h3225, h3229, h3230, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h3218, h3223, h3229, hc12, hlam, hphi, ht23, u3elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3234 | h3234
            · linarith only [h1, h3, h3234, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3236 | h3236
              · linarith only [h2, h3, h3236, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3238 | h3238
                · linarith only [h0, h3166, h3238, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3240 | h3240
                  · linarith only [h0, h3196, h3240, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3242 | h3242
                    · linarith only [h0, h3216, h3242, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3244 | h3244
                      · linarith only [h1, h3, h3218, h3244, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3246 | h3246
                        · linarith only [h2, h3, h3234, h3244, h3246, hlam]
                        · linarith only [h2, h3, h3238, h3244, h3246, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 6720000 in
set_option maxHeartbeats 6720000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s2 m hb0 hb2 hb3 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3249 | h3249
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3250 | h3250
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3251 | h3251
        · linarith only [h0, h2, h3251, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3253 | h3253
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3254 | h3254
            · linarith only [h1, h2, h3254, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3256 | h3256
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3257 | h3257
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3258 | h3258
                  · linarith only [h0, h2, h3254, h3258, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2, h3250, h3254, h3258, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h0, h2, h3250, h3254, h3256, h3257, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3262 | h3262
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3263 | h3263
                  · linarith only [h0, h2, h3254, h3263, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3250, h3251, h3263, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h3253, h3262, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3267 | h3267
            · linarith only [h1, h2, h3267, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3269 | h3269
              · linarith only [h3250, h3253, h3267, h3269, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3271 | h3271
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3272 | h3272
                  · linarith only [h0, h2, h3267, h3272, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3250, h3251, h3272, hc12, hc24, hlam, hphi]
                · linarith only [h2, h3249, h3271, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3276 | h3276
        · linarith only [h0, h2, h3276, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3278 | h3278
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3279 | h3279
            · linarith only [h1, h2, h3279, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3281 | h3281
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3282 | h3282
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3283 | h3283
                  · linarith only [h0, h3250, h3283, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3285 | h3285
                    · linarith only [h1, h2, h3276, h3283, h3285, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3287 | h3287
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3288 | h3288
                        · linarith only [h1, h2, h3279, h3288, hlam]
                        · linarith only [h1, h2, h3283, h3287, h3288, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h3250, h3278, h3279, h3287, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1, h2, h3250, h3278, h3279, h3282, hc13, hlam, hphi, u3elo3]
              · linarith only [h3250, h3278, h3281, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3294 | h3294
            · linarith only [h1, h2, h3294, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3296 | h3296
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3297 | h3297
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3298 | h3298
                  · linarith only [h0, h3278, h3294, h3296, h3298, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3300 | h3300
                    · linarith only [h3276, h3298, h3300, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3302 | h3302
                      · linarith only [h0, h3278, h3302, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3304 | h3304
                        · linarith only [h3294, h3304, hc03, hlam, hphi, u3elo1]
                        · linarith only [h2, h3249, h3302, h3304, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h0, h2, h3294, h3296, h3297, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3308 | h3308
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3309 | h3309
                  · linarith only [h0, h2, h3250, h3309, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3311 | h3311
                    · linarith only [h0, h2, h3250, h3276, h3311, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3313 | h3313
                      · linarith only [h3278, h3309, h3313, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3315 | h3315
                        · linarith only [h1, h2, h3294, h3315, hlam]
                        · linarith only [h1, h2, h3315, hc13, hlam, hphi, u3elo3]
                · linarith only [h2, h3249, h3308, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3319 | h3319
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3320 | h3320
        · linarith only [h0, h2, h3320, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3322 | h3322
          · linarith only [h0, h3249, h3322, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3324 | h3324
            · linarith only [h1, h2, h3324, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3326 | h3326
              · linarith only [h0, h3249, h3319, h3326, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3328 | h3328
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3329 | h3329
                  · linarith only [h0, h3249, h3324, h3328, h3329, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3319, h3320, h3329, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3332 | h3332
                  · linarith only [h0, h2, h3326, h3328, h3332, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h2, h3319, h3326, h3328, h3332, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3335 | h3335
        · linarith only [h0, h2, h3335, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3337 | h3337
          · linarith only [h0, h3249, h3319, h3337, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3339 | h3339
            · linarith only [h1, h2, h3339, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3341 | h3341
              · linarith only [h0, h3249, h3339, h3341, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3343 | h3343
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3344 | h3344
                  · linarith only [h0, h3319, h3339, h3344, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3346 | h3346
                    · linarith only [h1, h3249, h3335, h3343, h3344, h3346, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3348 | h3348
                      · linarith only [h1, h3249, h3337, h3344, h3348, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3350 | h3350
                        · linarith only [h1, h3249, h3339, h3343, h3350, hlam]
                        · linarith only [h1, h2, h3344, h3350, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3353 | h3353
                  · linarith only [h0, h3319, h3353, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3355 | h3355
                    · linarith only [h1, h2, h3343, h3353, h3355, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3357 | h3357
                      · linarith only [h0, h3337, h3357, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3359 | h3359
                        · linarith only [h1, h2, h3343, h3359, hc34, hc45, hlam, hphi]
                        · linarith only [h1, h2, h3353, h3359, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6724000 in
set_option maxHeartbeats 6724000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s1 m hb0 hb2 hb3 h0 h1
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
