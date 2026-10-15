import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S0
import Jsp000404.R1LeavesN7_0S1
import Jsp000404.R1LeavesN7_0S2
import Jsp000404.R1LeavesN7_0S3
import Jsp000404.R1LeavesN7_0S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 5) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 5) ∧ (m.d 1 4) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 4) ≤ z)))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2593 | h2593
  · rcases p1737_3 (m.d 1 2) (by simp) with h2594 | h2594
    · rcases p1737_3 (m.d 1 3) (by simp) with h2595 | h2595
      · linarith only [h2595, h437, hlam]
      · rcases p1737_3 (m.d 1 4) (by simp) with h2597 | h2597
        · linarith only [h2597, h498, hlam]
        · rcases p1737_3 (m.d 1 5) (by simp) with h2599 | h2599
          · rcases h1emax with h2600 | h2600 | h2600 | h2600 | h2600
            · linarith only [h0, h12, h2600, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h11, h12, h2600, h912, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1737_1]
            · rcases h2bigk with h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c | h2603c
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h0, h11, h12, h912, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h11, h4, h437, h7, h9, h912, h918, hlam, p1737_1, p2603_2]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h11, h4, h437, h7, h9, h918, hlam, p1737_1, p2603_2]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                rcases p2603_3 (m.d 0 2) (by simp) with h2608 | h2608
                · rcases p2603_3 (m.d 1 2) (by simp) with h2609 | h2609
                  · linarith only [h0, h2609, hlam]
                  · linarith only [h12, h2609, hlam]
                · linarith only [h2608, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h0, hlam, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                rcases p2603_3 (m.d 0 2) (by simp) with h2615 | h2615
                · rcases p2603_3 (m.d 1 2) (by simp) with h2616 | h2616
                  · rcases p2603_3 (m.d 2 3) (by simp) with h2617 | h2617
                    · linarith only [h2617, hlam, p2603_0]
                    · rcases p2603_3 (m.d 2 4) (by simp) with h2619 | h2619
                      · linarith only [h11, h2619, hlam]
                      · linarith only [h2619, h912, hlam]
                  · linarith only [h2616, hlam, p2603_0]
                · linarith only [h2615, h4, hlam]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                rcases p2603_3 (m.d 0 2) (by simp) with h2624 | h2624
                · rcases p2603_3 (m.d 1 2) (by simp) with h2625 | h2625
                  · rcases p2603_3 (m.d 2 3) (by simp) with h2626 | h2626
                    · linarith only [h10, h2626, hlam]
                    · rcases p2603_3 (m.d 2 4) (by simp) with h2628 | h2628
                      · linarith only [h2628, hlam, p2603_0]
                      · rcases p2603_3 (m.d 2 5) (by simp) with h2630 | h2630
                        · linarith only [h12, h2630, hlam]
                        · linarith only [h2630, h916, hlam]
                  · linarith only [h2625, hlam, p2603_0]
                · linarith only [h2624, h5, hlam]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                rcases p2603_3 (m.d 0 2) (by simp) with h2635 | h2635
                · rcases p2603_3 (m.d 1 2) (by simp) with h2636 | h2636
                  · rcases p2603_3 (m.d 2 3) (by simp) with h2637 | h2637
                    · linarith only [h10, h2637, hlam]
                    · rcases p2603_3 (m.d 2 4) (by simp) with h2639 | h2639
                      · linarith only [h11, h2639, hlam]
                      · rcases p2603_3 (m.d 2 5) (by simp) with h2641 | h2641
                        · linarith only [h2641, hlam, p2603_0]
                        · rcases h4bigk with h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c | h2643c
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h437, h9, h918, hlam, p1737_1, p2643_2]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h11, h437, h9, h918, hlam, p1737_1, p2643_2]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            rcases p2643_3 (m.d 0 4) (by simp) with h2647 | h2647
                            · rcases p2643_3 (m.d 1 4) (by simp) with h2648 | h2648
                              · linarith only [h2, h2648, hlam]
                              · rcases p2643_3 (m.d 2 4) (by simp) with h2650 | h2650
                                · linarith only [h2650, h5, hlam]
                                · rcases p2643_3 (m.d 3 4) (by simp) with h2652 | h2652
                                  · linarith only [h2652, h7, hlam]
                                  · rcases p2643_3 (m.d 4 5) (by simp) with h2654 | h2654
                                    · linarith only [h2654, h9, hlam]
                                    · linarith only [h2654, h918, hlam]
                            · linarith only [h2647, h7, hlam]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h11, h4, h437, h7, h912, h918, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h2, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h437, h9, h912, h918, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h13, hlam, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h498, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h5, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h11, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h912, hlam, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h916, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h7, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h918, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h9, hlam, p2643_0]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            rcases p2643_3 (m.d 0 4) (by simp) with h2675 | h2675
                            · rcases p2643_3 (m.d 1 4) (by simp) with h2676 | h2676
                              · linarith only [h2676, hlam, p2643_0]
                              · rcases p2643_3 (m.d 2 4) (by simp) with h2678 | h2678
                                · linarith only [h2678, h916, hlam]
                                · rcases p2643_3 (m.d 3 4) (by simp) with h2680 | h2680
                                  · linarith only [h2680, h918, hlam]
                                  · linarith only [h13, h2680, hlam]
                            · linarith only [h2, h2675, hlam]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            rcases p2643_3 (m.d 0 4) (by simp) with h2684 | h2684
                            · rcases p2643_3 (m.d 1 4) (by simp) with h2685 | h2685
                              · linarith only [h2685, h498, hlam]
                              · linarith only [h11, h2685, hlam]
                            · linarith only [h2684, h5, hlam]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2643_1]
                          · have p2643_0 := h2643c.1
                            have p2643_1 := h2643c.2.1
                            have p2643_2 := h2643c.2.2.1
                            have p2643_3 := h2643c.2.2.2
                            linarith only [hlam, p2643_0]
                  · linarith only [h2636, hlam, p2603_0]
                · linarith only [h2635, h6, hlam]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h4, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h10, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h912, hlam, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h914, hlam, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h5, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h11, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h916, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h6, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h12, hlam, p2603_0]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2603_1]
              · have p2603_0 := h2603c.1
                have p2603_1 := h2603c.2.1
                have p2603_2 := h2603c.2.2.1
                have p2603_3 := h2603c.2.2.2
                linarith only [hlam, p2603_0]
            · rcases h2bigk with h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h0, h12, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h11, h4, h437, h7, h9, h912, h918, hlam, p1737_1, p2708_2]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h11, h4, h437, h7, h9, h918, hlam, p1737_1, p2708_2]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                rcases p2708_3 (m.d 0 2) (by simp) with h2713 | h2713
                · rcases p2708_3 (m.d 1 2) (by simp) with h2714 | h2714
                  · linarith only [h0, h2714, hlam]
                  · linarith only [h12, h2714, hlam]
                · linarith only [h2713, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h0, hlam, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                rcases p2708_3 (m.d 0 2) (by simp) with h2720 | h2720
                · rcases p2708_3 (m.d 1 2) (by simp) with h2721 | h2721
                  · rcases p2708_3 (m.d 2 3) (by simp) with h2722 | h2722
                    · linarith only [h2722, hlam, p2708_0]
                    · rcases p2708_3 (m.d 2 4) (by simp) with h2724 | h2724
                      · linarith only [h11, h2724, hlam]
                      · linarith only [h2724, h912, hlam]
                  · linarith only [h2721, hlam, p2708_0]
                · linarith only [h2720, h4, hlam]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                rcases p2708_3 (m.d 0 2) (by simp) with h2729 | h2729
                · rcases p2708_3 (m.d 1 2) (by simp) with h2730 | h2730
                  · rcases p2708_3 (m.d 2 3) (by simp) with h2731 | h2731
                    · linarith only [h10, h2731, hlam]
                    · rcases p2708_3 (m.d 2 4) (by simp) with h2733 | h2733
                      · linarith only [h2733, hlam, p2708_0]
                      · rcases p2708_3 (m.d 2 5) (by simp) with h2735 | h2735
                        · linarith only [h12, h2735, hlam]
                        · linarith only [h2735, h916, hlam]
                  · linarith only [h2730, hlam, p2708_0]
                · linarith only [h2729, h5, hlam]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                rcases p2708_3 (m.d 0 2) (by simp) with h2740 | h2740
                · rcases p2708_3 (m.d 1 2) (by simp) with h2741 | h2741
                  · rcases p2708_3 (m.d 2 3) (by simp) with h2742 | h2742
                    · linarith only [h10, h2742, hlam]
                    · rcases p2708_3 (m.d 2 4) (by simp) with h2744 | h2744
                      · linarith only [h11, h2744, hlam]
                      · rcases p2708_3 (m.d 2 5) (by simp) with h2746 | h2746
                        · linarith only [h2746, hlam, p2708_0]
                        · rcases h4bigk with h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h437, h9, h918, hlam, p1737_1, p2748_2]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h11, h437, h9, h918, hlam, p1737_1, p2748_2]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            rcases p2748_3 (m.d 0 4) (by simp) with h2752 | h2752
                            · rcases p2748_3 (m.d 1 4) (by simp) with h2753 | h2753
                              · linarith only [h2, h2753, hlam]
                              · rcases p2748_3 (m.d 2 4) (by simp) with h2755 | h2755
                                · linarith only [h2755, h5, hlam]
                                · rcases p2748_3 (m.d 3 4) (by simp) with h2757 | h2757
                                  · linarith only [h2757, h7, hlam]
                                  · rcases p2748_3 (m.d 4 5) (by simp) with h2759 | h2759
                                    · linarith only [h2759, h9, hlam]
                                    · linarith only [h2759, h918, hlam]
                            · linarith only [h2752, h7, hlam]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h0, h4, h437, h7, h918, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h2, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h12, h912, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1737_1, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h13, hlam, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h498, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h5, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h11, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h912, hlam, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h916, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h7, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h0, h4, h7, h9, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h918, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h9, hlam, p2748_0]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            rcases p2748_3 (m.d 0 4) (by simp) with h2780 | h2780
                            · rcases p2748_3 (m.d 1 4) (by simp) with h2781 | h2781
                              · linarith only [h2781, hlam, p2748_0]
                              · rcases p2748_3 (m.d 2 4) (by simp) with h2783 | h2783
                                · linarith only [h2783, h916, hlam]
                                · rcases p2748_3 (m.d 3 4) (by simp) with h2785 | h2785
                                  · linarith only [h2785, h918, hlam]
                                  · linarith only [h13, h2785, hlam]
                            · linarith only [h2, h2780, hlam]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            rcases p2748_3 (m.d 0 4) (by simp) with h2789 | h2789
                            · rcases p2748_3 (m.d 1 4) (by simp) with h2790 | h2790
                              · linarith only [h2790, h498, hlam]
                              · linarith only [h11, h2790, hlam]
                            · linarith only [h2789, h5, hlam]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2748_1]
                          · have p2748_0 := h2748c.1
                            have p2748_1 := h2748c.2.1
                            have p2748_2 := h2748c.2.2.1
                            have p2748_3 := h2748c.2.2.2
                            linarith only [hlam, p2748_0]
                  · linarith only [h2741, hlam, p2708_0]
                · linarith only [h2740, h6, hlam]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h4, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h10, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h912, hlam, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h914, hlam, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h5, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h11, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h916, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h6, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h12, hlam, p2708_0]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2708_1]
              · have p2708_0 := h2708c.1
                have p2708_1 := h2708c.2.1
                have p2708_2 := h2708c.2.2.1
                have p2708_3 := h2708c.2.2.2
                linarith only [hlam, p2708_0]
            · linarith only [h2600, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1737_1]
          · linarith only [h2599, h498, hlam]
    · linarith only [h11, h2594, hlam]
  · linarith only [h2, h2593, hlam]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 5) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 5) ∧ (m.d 1 5) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 5) ≤ z)))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases h1bigk with h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x2 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x3 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x4 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x5 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x6 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x7 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x8 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x9 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x10 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x11 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x12 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x13 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x14 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x15 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x16 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x17 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x18 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x19 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x20 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x21 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x22 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x23 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x24 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918 h1737c

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916 h918

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914 h916

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 2 3 5 (by decide) (by decide) with h914 | h914
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912 h914

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 2 3 4 (by decide) (by decide) with h912 | h912
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498 h912

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 1 4 5 (by decide) (by decide) with h498 | h498
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437 h498

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 1 3 5 (by decide) (by decide) with h437 | h437
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13 h437

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 h13

set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  · rcases m.htr 1 3 4 (by decide) (by decide) with h2818 | h2818
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2819 | h2819
      · linarith only [h10, h12, h2819, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2821 | h2821
        · linarith only [h11, h12, h2821, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2823 | h2823
          · linarith only [h0, h10, h12, h2823, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h12, h2818, h2823, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2826 | h2826
      · linarith only [h11, h12, h2818, h2826, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2828 | h2828
        · linarith only [h11, h12, h2828, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2830 | h2830
          · linarith only [h0, h10, h12, h2818, h2830, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2832 | h2832
            · linarith only [h10, h12, h2826, h2832, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2834 | h2834
              · linarith only [h0, h11, h12, h2834, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2836 | h2836
                · linarith only [h11, h12, h2830, h2834, h2836, hc23, hc34, hlam, hphi]
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
                    rcases p2838_3 (m.d 0 1) (by simp) with h2840 | h2840
                    · rcases p2838_3 (m.d 1 2) (by simp) with h2841 | h2841
                      · linarith only [h2841, hlam, p2838_0]
                      · rcases p2838_3 (m.d 1 3) (by simp) with h2843 | h2843
                        · linarith only [h1, h2843, hlam]
                        · rcases p2838_3 (m.d 1 4) (by simp) with h2845 | h2845
                          · linarith only [h2, h2845, hlam]
                          · rcases p2838_3 (m.d 1 5) (by simp) with h2847 | h2847
                            · linarith only [h2847, h3, hlam]
                            · linarith only [h12, h2847, hlam]
                    · linarith only [h2840, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h0, h2818, h2836, h4, h7, h9, hlam, p2838_2]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    rcases p2838_3 (m.d 0 1) (by simp) with h2852 | h2852
                    · rcases p2838_3 (m.d 1 2) (by simp) with h2853 | h2853
                      · linarith only [h0, h2853, hlam]
                      · linarith only [h11, h2853, hlam]
                    · linarith only [h2852, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    rcases p2838_3 (m.d 0 1) (by simp) with h2857 | h2857
                    · rcases p2838_3 (m.d 1 2) (by simp) with h2858 | h2858
                      · linarith only [h0, h2858, hlam]
                      · rcases p2838_3 (m.d 1 3) (by simp) with h2860 | h2860
                        · linarith only [h1, h2860, hlam]
                        · rcases p2838_3 (m.d 1 4) (by simp) with h2862 | h2862
                          · linarith only [h2, h2862, hlam]
                          · rcases p2838_3 (m.d 1 5) (by simp) with h2864 | h2864
                            · linarith only [h2864, hlam, p2838_0]
                            · rcases h1emax with h2866 | h2866 | h2866 | h2866 | h2866
                              · linarith only [h0, h11, h12, h2830, h2832, h2836, h2866, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases h2bigk with h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c | h2868c
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  rcases p2868_3 (m.d 0 2) (by simp) with h2870 | h2870
                                  · rcases p2868_3 (m.d 1 2) (by simp) with h2871 | h2871
                                    · linarith only [h0, h2871, hlam]
                                    · rcases p2868_3 (m.d 2 3) (by simp) with h2873 | h2873
                                      · linarith only [h2873, h4, hlam]
                                      · rcases p2868_3 (m.d 2 4) (by simp) with h2875 | h2875
                                        · linarith only [h2875, h5, hlam]
                                        · rcases p2868_3 (m.d 2 5) (by simp) with h2877 | h2877
                                          · linarith only [h2877, h6, hlam]
                                          · linarith only [h12, h2877, hlam]
                                  · linarith only [h0, h2870, hlam]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h11, h12, h2830, h2832, h2836, h4, h7, h9, hlam, p2868_2]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h11, h12, h2832, h2836, h4, h7, h9, hlam, p2868_2]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h0, h11, h12, h2830, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h0, hlam, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h12, h2832, h2836, h7, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h12, h2832, h2836, h7, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h12, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h4, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h10, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h2830, hlam, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h2832, hlam, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h5, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h11, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h0, h11, h12, h2832, h2836, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h2834, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h6, hlam, p2868_0]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [h0, h10, h2832, h2836, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2868_1]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  rcases p2868_3 (m.d 0 2) (by simp) with h2901 | h2901
                                  · rcases p2868_3 (m.d 1 2) (by simp) with h2902 | h2902
                                    · linarith only [h12, h2902, hlam]
                                    · linarith only [h10, h2902, hlam]
                                  · linarith only [h2901, h4, hlam]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  rcases p2868_3 (m.d 0 2) (by simp) with h2906 | h2906
                                  · rcases p2868_3 (m.d 1 2) (by simp) with h2907 | h2907
                                    · linarith only [h12, h2907, hlam]
                                    · linarith only [h11, h2907, hlam]
                                  · linarith only [h2906, h5, hlam]
                                · have p2868_0 := h2868c.1
                                  have p2868_1 := h2868c.2.1
                                  have p2868_2 := h2868c.2.2.1
                                  have p2868_3 := h2868c.2.2.2
                                  linarith only [hlam, p2868_0]
                              · rcases h2bigk with h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  rcases p2912_3 (m.d 0 2) (by simp) with h2914 | h2914
                                  · rcases p2912_3 (m.d 1 2) (by simp) with h2915 | h2915
                                    · linarith only [h0, h2915, hlam]
                                    · rcases p2912_3 (m.d 2 3) (by simp) with h2917 | h2917
                                      · linarith only [h2917, h4, hlam]
                                      · rcases p2912_3 (m.d 2 4) (by simp) with h2919 | h2919
                                        · linarith only [h2919, h5, hlam]
                                        · rcases p2912_3 (m.d 2 5) (by simp) with h2921 | h2921
                                          · linarith only [h2921, h6, hlam]
                                          · linarith only [h12, h2921, hlam]
                                  · linarith only [h0, h2914, hlam]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h10, h2818, h2836, h4, h7, h9, hlam, p2912_2]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h11, h12, h2832, h2836, h4, h7, h9, hlam, p2912_2]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h0, h11, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h0, hlam, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h0, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h0, h12, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h12, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h4, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h10, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h2830, hlam, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h2832, hlam, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h5, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h11, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h0, h11, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h2834, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h6, hlam, p2912_0]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2912_1]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  rcases p2912_3 (m.d 0 2) (by simp) with h2945 | h2945
                                  · rcases p2912_3 (m.d 1 2) (by simp) with h2946 | h2946
                                    · linarith only [h12, h2946, hlam]
                                    · linarith only [h10, h2946, hlam]
                                  · linarith only [h2945, h4, hlam]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  rcases p2912_3 (m.d 0 2) (by simp) with h2950 | h2950
                                  · rcases p2912_3 (m.d 1 2) (by simp) with h2951 | h2951
                                    · linarith only [h12, h2951, hlam]
                                    · linarith only [h11, h2951, hlam]
                                  · linarith only [h2950, h5, hlam]
                                · have p2912_0 := h2912c.1
                                  have p2912_1 := h2912c.2.1
                                  have p2912_2 := h2912c.2.2.1
                                  have p2912_3 := h2912c.2.2.2
                                  linarith only [hlam, p2912_0]
                              · rcases h2bigk with h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  rcases p2956_3 (m.d 0 2) (by simp) with h2958 | h2958
                                  · rcases p2956_3 (m.d 1 2) (by simp) with h2959 | h2959
                                    · linarith only [h0, h2959, hlam]
                                    · rcases p2956_3 (m.d 2 3) (by simp) with h2961 | h2961
                                      · linarith only [h2961, h4, hlam]
                                      · rcases p2956_3 (m.d 2 4) (by simp) with h2963 | h2963
                                        · linarith only [h2963, h5, hlam]
                                        · rcases p2956_3 (m.d 2 5) (by simp) with h2965 | h2965
                                          · linarith only [h2965, h6, hlam]
                                          · linarith only [h12, h2965, hlam]
                                  · linarith only [h0, h2958, hlam]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h10, h2818, h2836, h4, h7, h9, hlam, p2956_2]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h11, h12, h2832, h2836, h4, h7, h9, hlam, p2956_2]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h0, h11, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h0, hlam, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h0, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h0, h12, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h12, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h4, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h10, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h2830, hlam, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h2832, hlam, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h5, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h11, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h0, h11, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h2834, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h6, hlam, p2956_0]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2956_1]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  rcases p2956_3 (m.d 0 2) (by simp) with h2989 | h2989
                                  · rcases p2956_3 (m.d 1 2) (by simp) with h2990 | h2990
                                    · linarith only [h12, h2990, hlam]
                                    · linarith only [h10, h2990, hlam]
                                  · linarith only [h2989, h4, hlam]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  rcases p2956_3 (m.d 0 2) (by simp) with h2994 | h2994
                                  · rcases p2956_3 (m.d 1 2) (by simp) with h2995 | h2995
                                    · linarith only [h12, h2995, hlam]
                                    · linarith only [h11, h2995, hlam]
                                  · linarith only [h2994, h5, hlam]
                                · have p2956_0 := h2956c.1
                                  have p2956_1 := h2956c.2.1
                                  have p2956_2 := h2956c.2.2.1
                                  have p2956_3 := h2956c.2.2.2
                                  linarith only [hlam, p2956_0]
                              · rcases h2bigk with h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  rcases p3000_3 (m.d 0 2) (by simp) with h3002 | h3002
                                  · rcases p3000_3 (m.d 1 2) (by simp) with h3003 | h3003
                                    · linarith only [h0, h3003, hlam]
                                    · rcases p3000_3 (m.d 2 3) (by simp) with h3005 | h3005
                                      · linarith only [h3005, h4, hlam]
                                      · rcases p3000_3 (m.d 2 4) (by simp) with h3007 | h3007
                                        · linarith only [h3007, h5, hlam]
                                        · rcases p3000_3 (m.d 2 5) (by simp) with h3009 | h3009
                                          · linarith only [h3009, h6, hlam]
                                          · linarith only [h12, h3009, hlam]
                                  · linarith only [h0, h3002, hlam]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h10, h12, h2832, h2836, h4, h7, h9, hlam, p3000_2]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h11, h12, h2832, h2836, h4, h7, h9, hlam, p3000_2]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h0, h11, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h0, hlam, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h0, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h0, h12, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h12, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h4, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h10, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h2830, hlam, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h2832, hlam, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h5, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h11, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h11, h12, h2866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h2834, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h6, hlam, p3000_0]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [h0, h11, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3000_1]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  rcases p3000_3 (m.d 0 2) (by simp) with h3033 | h3033
                                  · rcases p3000_3 (m.d 1 2) (by simp) with h3034 | h3034
                                    · linarith only [h12, h3034, hlam]
                                    · linarith only [h10, h3034, hlam]
                                  · linarith only [h3033, h4, hlam]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  rcases p3000_3 (m.d 0 2) (by simp) with h3038 | h3038
                                  · rcases p3000_3 (m.d 1 2) (by simp) with h3039 | h3039
                                    · linarith only [h12, h3039, hlam]
                                    · linarith only [h11, h3039, hlam]
                                  · linarith only [h3038, h5, hlam]
                                · have p3000_0 := h3000c.1
                                  have p3000_1 := h3000c.2.1
                                  have p3000_2 := h3000c.2.2.1
                                  have p3000_3 := h3000c.2.2.2
                                  linarith only [hlam, p3000_0]
                    · linarith only [h2857, hlam, p2838_0]
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
                    linarith only [h0, h12, h2832, h2836, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h0, h12, h2832, h2836, h4, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h12, hlam, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h1, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h10, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h2818, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h2826, hlam, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h2, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h11, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h0, h10, h11, h12, h2832, h2836, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h2828, hlam, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h3, hlam, p2838_0]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2838_1]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    rcases p2838_3 (m.d 0 1) (by simp) with h3062 | h3062
                    · rcases p2838_3 (m.d 1 2) (by simp) with h3063 | h3063
                      · linarith only [h12, h3063, hlam]
                      · linarith only [h10, h3063, hlam]
                    · linarith only [h1, h3062, hlam]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    rcases p2838_3 (m.d 0 1) (by simp) with h3067 | h3067
                    · rcases p2838_3 (m.d 1 2) (by simp) with h3068 | h3068
                      · linarith only [h12, h3068, hlam]
                      · linarith only [h11, h3068, hlam]
                    · linarith only [h2, h3067, hlam]
                  · have p2838_0 := h2838c.1
                    have p2838_1 := h2838c.2.1
                    have p2838_2 := h2838c.2.2.1
                    have p2838_3 := h2838c.2.2.2
                    linarith only [hlam, p2838_0]

end R2N4
