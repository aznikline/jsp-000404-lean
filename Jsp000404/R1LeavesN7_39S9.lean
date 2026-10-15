import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S7
import Jsp000404.R1LeavesN7_39S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1894 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2052 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2147 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2733 | h2733
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2734 | h2734
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2735 | h2735
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2736 | h2736
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2737 | h2737
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2738 | h2738
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2739 | h2739
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2740 | h2740
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2741 | h2741
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2742 | h2742
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2743 | h2743
                      · rcases h1bigk with h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h0, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h1769, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h1894, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2052, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          rcases p2744_3 (m.d 0 1) (by simp) with h2750 | h2750
                          · linarith only [h2750, hlam, p2744_0]
                          · rcases p2744_3 (m.d 1 2) (by simp) with h2752 | h2752
                            · rcases p2744_3 (m.d 1 3) (by simp) with h2753 | h2753
                              · linarith only [h2735, h2753, hlam]
                              · linarith only [h1769, h2753, hlam]
                            · linarith only [h2752, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h0, h2147, h2735, hc01, hc12, hlam, hphi, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          rcases p2744_3 (m.d 0 1) (by simp) with h2761 | h2761
                          · linarith only [h2761, hlam, p2744_0]
                          · rcases p2744_3 (m.d 1 2) (by simp) with h2763 | h2763
                            · rcases p2744_3 (m.d 1 3) (by simp) with h2764 | h2764
                              · rcases p2744_3 (m.d 1 4) (by simp) with h2765 | h2765
                                · linarith only [h2738, h2765, hlam]
                                · linarith only [h1894, h2765, hlam]
                              · linarith only [h2764, hlam, p2744_0]
                            · linarith only [h0, h2763, hlam]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2735, hlam, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2052, h2740, hc01, hc13, hlam, hphi, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2052, h2735, hc01, hc12, hlam, hphi, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          rcases p2744_3 (m.d 0 1) (by simp) with h2774 | h2774
                          · linarith only [h2774, hlam, p2744_0]
                          · rcases p2744_3 (m.d 1 2) (by simp) with h2776 | h2776
                            · rcases p2744_3 (m.d 1 3) (by simp) with h2777 | h2777
                              · rcases p2744_3 (m.d 1 4) (by simp) with h2778 | h2778
                                · rcases p2744_3 (m.d 1 5) (by simp) with h2779 | h2779
                                  · linarith only [h2740, h2779, hlam]
                                  · linarith only [h2052, h2779, hlam]
                                · linarith only [h2778, hlam, p2744_0]
                              · linarith only [h1769, h2777, hlam]
                            · linarith only [h0, h2776, hlam]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2736, hlam, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2738, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2052, hc01, hc14, hlam, hphi, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          rcases p2744_3 (m.d 0 1) (by simp) with h2789 | h2789
                          · linarith only [h2789, hlam, p2744_0]
                          · rcases p2744_3 (m.d 1 2) (by simp) with h2791 | h2791
                            · rcases p2744_3 (m.d 1 3) (by simp) with h2792 | h2792
                              · rcases p2744_3 (m.d 1 4) (by simp) with h2793 | h2793
                                · rcases p2744_3 (m.d 1 5) (by simp) with h2794 | h2794
                                  · rcases h3bigk with h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h1769, hlam, p2795_1]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2147, hlam, p2795_1]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2147, h2735, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2147, h2735, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2733, h2735, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h0, h2147, h2735, hc01, hc12, hlam, hphi, p2795_1]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      rcases p2795_3 (m.d 0 3) (by simp) with h2804 | h2804
                                      · linarith only [h1769, h2804, hlam]
                                      · linarith only [h2733, h2804, hlam]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      rcases p2795_3 (m.d 0 3) (by simp) with h2807 | h2807
                                      · linarith only [h1769, h2807, hlam]
                                      · linarith only [h2734, h2807, hlam]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2733, h2743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2735, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2735, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2735, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2733, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2738, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2741, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2733, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2795_1, u3ehi4]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2734, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2739, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2742, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [h2743, hlam, p2795_0]
                                    · have p2795_0 := h2795c.1
                                      have p2795_1 := h2795c.2.1
                                      have p2795_2 := h2795c.2.2.1
                                      have p2795_3 := h2795c.2.2.2
                                      linarith only [hlam, p2795_0]
                                  · linarith only [h2794, hlam, p2744_0]
                                · linarith only [h1894, h2793, hlam]
                              · linarith only [h1769, h2792, hlam]
                            · linarith only [h0, h2791, hlam]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2737, hlam, p2744_1]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2739, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [h2740, hlam, p2744_0]
                        · have p2744_0 := h2744c.1
                          have p2744_1 := h2744c.2.1
                          have p2744_2 := h2744c.2.2.1
                          have p2744_3 := h2744c.2.2.2
                          linarith only [hlam, p2744_0]
                      · rcases h1bigk with h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h0, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h1769, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h1894, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2052, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          rcases p2833_3 (m.d 0 1) (by simp) with h2839 | h2839
                          · linarith only [h2839, hlam, p2833_0]
                          · rcases p2833_3 (m.d 1 2) (by simp) with h2841 | h2841
                            · rcases p2833_3 (m.d 1 3) (by simp) with h2842 | h2842
                              · linarith only [h2735, h2842, hlam]
                              · linarith only [h1769, h2842, hlam]
                            · linarith only [h2841, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2738, h2740, h2743, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2833_1]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2740, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2833_1, u3ehi3]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2833_1]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          rcases p2833_3 (m.d 0 1) (by simp) with h2850 | h2850
                          · linarith only [h2850, hlam, p2833_0]
                          · rcases p2833_3 (m.d 1 2) (by simp) with h2852 | h2852
                            · rcases p2833_3 (m.d 1 3) (by simp) with h2853 | h2853
                              · rcases p2833_3 (m.d 1 4) (by simp) with h2854 | h2854
                                · linarith only [h2738, h2854, hlam]
                                · linarith only [h1894, h2854, hlam]
                              · linarith only [h2853, hlam, p2833_0]
                            · linarith only [h0, h2852, hlam]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2735, hlam, p2833_1]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2740, h2743, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2833_1, u3ehi3]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2735, h2740, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2833_1, u3ehi3]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          rcases p2833_3 (m.d 0 1) (by simp) with h2863 | h2863
                          · linarith only [h2863, hlam, p2833_0]
                          · rcases p2833_3 (m.d 1 2) (by simp) with h2865 | h2865
                            · rcases p2833_3 (m.d 1 3) (by simp) with h2866 | h2866
                              · rcases p2833_3 (m.d 1 4) (by simp) with h2867 | h2867
                                · rcases p2833_3 (m.d 1 5) (by simp) with h2868 | h2868
                                  · linarith only [h2740, h2868, hlam]
                                  · linarith only [h2052, h2868, hlam]
                                · linarith only [h2867, hlam, p2833_0]
                              · linarith only [h1769, h2866, hlam]
                            · linarith only [h0, h2865, hlam]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2736, hlam, p2833_1]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2738, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2740, h2743, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2833_1, u3ehi3]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          rcases p2833_3 (m.d 0 1) (by simp) with h2878 | h2878
                          · linarith only [h2878, hlam, p2833_0]
                          · rcases p2833_3 (m.d 1 2) (by simp) with h2880 | h2880
                            · rcases p2833_3 (m.d 1 3) (by simp) with h2881 | h2881
                              · rcases p2833_3 (m.d 1 4) (by simp) with h2882 | h2882
                                · rcases p2833_3 (m.d 1 5) (by simp) with h2883 | h2883
                                  · rcases h3bigk with h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h1769, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2147, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2147, h2735, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2147, h2735, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2733, h2735, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h0, h2147, h2735, hc01, hc12, hlam, hphi, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      rcases p2884_3 (m.d 0 3) (by simp) with h2893 | h2893
                                      · linarith only [h1769, h2893, hlam]
                                      · linarith only [h2733, h2893, hlam]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      rcases p2884_3 (m.d 0 3) (by simp) with h2896 | h2896
                                      · linarith only [h1769, h2896, hlam]
                                      · linarith only [h2734, h2896, hlam]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2734, h2743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2735, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2735, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2735, h2743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2733, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2738, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2741, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2743, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2734, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2739, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2742, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2734, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2884_1, u3ehi3]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                  · linarith only [h2883, hlam, p2833_0]
                                · linarith only [h1894, h2882, hlam]
                              · linarith only [h1769, h2881, hlam]
                            · linarith only [h0, h2880, hlam]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2737, hlam, p2833_1]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2739, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [h2740, hlam, p2833_0]
                        · have p2833_0 := h2833c.1
                          have p2833_1 := h2833c.2.1
                          have p2833_2 := h2833c.2.2.1
                          have p2833_3 := h2833c.2.2.2
                          linarith only [hlam, p2833_0]
                    · linarith only [h2147, h2734, h2742, hlam]
                  · linarith only [h2147, h2734, h2741, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2924 | h2924
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2925 | h2925
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2926 | h2926
                      · linarith only [h1894, h2733, h2740, h2926, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h0, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1769, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1894, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2052, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          rcases p2928_3 (m.d 0 1) (by simp) with h2934 | h2934
                          · linarith only [h2934, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 2) (by simp) with h2936 | h2936
                            · rcases p2928_3 (m.d 1 3) (by simp) with h2937 | h2937
                              · linarith only [h2735, h2937, hlam]
                              · linarith only [h1769, h2937, hlam]
                            · linarith only [h2936, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1769, hc01, hc12, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          rcases p2928_3 (m.d 0 1) (by simp) with h2945 | h2945
                          · linarith only [h2945, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 2) (by simp) with h2947 | h2947
                            · rcases p2928_3 (m.d 1 3) (by simp) with h2948 | h2948
                              · rcases p2928_3 (m.d 1 4) (by simp) with h2949 | h2949
                                · linarith only [h2738, h2949, hlam]
                                · linarith only [h1894, h2949, hlam]
                              · linarith only [h2948, hlam, p2928_0]
                            · linarith only [h0, h2947, hlam]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2735, hlam, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1894, hc01, hc13, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1894, h2735, h2740, hc01, hc12, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2147, h2734, h2735, h2740, h2926, hc01, hc12, hc45, hlam, hphi, ht34, p2928_1, u3ehi3]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2736, hlam, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2738, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2740, hlam, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          rcases p2928_3 (m.d 0 1) (by simp) with h2963 | h2963
                          · linarith only [h2963, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 2) (by simp) with h2965 | h2965
                            · rcases p2928_3 (m.d 1 3) (by simp) with h2966 | h2966
                              · rcases p2928_3 (m.d 1 4) (by simp) with h2967 | h2967
                                · linarith only [h2740, h2967, hlam]
                                · linarith only [h1894, h2967, hlam]
                              · linarith only [h1769, h2966, hlam]
                            · linarith only [h0, h2965, hlam]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2737, hlam, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2739, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1894, hc01, hc15, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                    · linarith only [h2147, h2734, h2925, hlam]
                  · linarith only [h2147, h2734, h2924, hc34, hlam, hphi, u3ehi4]
              · linarith only [h2147, h2734, h2735, h2739, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h2147, h2733, h2735, h2738, hlam]
          · linarith only [h2147, h2733, h2735, h2737, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · linarith only [h2147, h2733, h2735, h2736, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2982 | h2982
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2983 | h2983
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2984 | h2984
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2985 | h2985
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2986 | h2986
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2987 | h2987
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2988 | h2988
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2989 | h2989
                      · rcases h1bigk with h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c | h2990c
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h0, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h1769, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h1894, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2052, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2735, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2735, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2052, h2735, h2986, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2052, h2735, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          rcases p2990_3 (m.d 0 1) (by simp) with h3001 | h3001
                          · linarith only [h3001, hlam, p2990_0]
                          · rcases p2990_3 (m.d 1 2) (by simp) with h3003 | h3003
                            · linarith only [h2735, h3003, hlam]
                            · linarith only [h0, h3003, hlam]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h0, hc01, hc13, hlam, hphi, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2052, h2735, h2986, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2052, h2735, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2735, h2982, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2982, hlam, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2984, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2052, h2735, h2982, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2735, h2983, hc01, hc23, hlam, hphi, ht12, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2983, hlam, p2990_1]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2985, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [h2986, hlam, p2990_0]
                        · have p2990_0 := h2990c.1
                          have p2990_1 := h2990c.2.1
                          have p2990_2 := h2990c.2.2.1
                          have p2990_3 := h2990c.2.2.2
                          linarith only [hlam, p2990_0]
                      · linarith only [h2735, h2982, h2986, h2989, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h2735, h2988, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2052, h2734, h2735, h2982, h2986, h2987, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3023 | h3023
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3024 | h3024
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3025 | h3025
                      · linarith only [h1894, h2735, h2982, h2986, h3023, h3025, hc01, hc23, hlam, hphi, ht12]
                      · rcases h1bigk with h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c | h3027c
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h0, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1769, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1894, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2052, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2735, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2735, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1894, h2735, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1894, h2735, h2986, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          rcases p3027_3 (m.d 0 1) (by simp) with h3038 | h3038
                          · linarith only [h3038, hlam, p3027_0]
                          · rcases p3027_3 (m.d 1 2) (by simp) with h3040 | h3040
                            · linarith only [h2735, h3040, hlam]
                            · linarith only [h0, h3040, hlam]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2735, h2983, h3024, h3025, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3027_1, u3ehi3]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1894, h2735, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1894, h2735, h2986, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2986, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2982, hlam, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2984, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2986, hlam, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2735, h2983, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2983, hlam, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h2985, hlam, p3027_0]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [h1894, h2735, h2983, hc01, hc23, hlam, hphi, ht12, p3027_1]
                        · have p3027_0 := h3027c.1
                          have p3027_1 := h3027c.2.1
                          have p3027_2 := h3027c.2.2.1
                          have p3027_3 := h3027c.2.2.2
                          linarith only [hlam, p3027_0]
                    · linarith only [h0, h2735, h3024, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1894, h2733, h2735, h2983, h2986, h3023, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h1769, h2733, h2985, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1769, h2733, h2984, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3061 | h3061
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3062 | h3062
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3063 | h3063
                · linarith only [h2982, h2983, h3063, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3065 | h3065
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3066 | h3066
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3067 | h3067
                      · linarith only [h1894, h2982, h2983, h3063, h3065, h3066, h3067, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h1bigk with h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h0, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h1769, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h1894, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2052, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2983, hc01, hc25, hlam, hphi, ht12, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2735, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h1894, h2983, hc01, hc25, hlam, hphi, ht12, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2983, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          rcases p3069_3 (m.d 0 1) (by simp) with h3080 | h3080
                          · linarith only [h3080, hlam, p3069_0]
                          · rcases p3069_3 (m.d 1 2) (by simp) with h3082 | h3082
                            · linarith only [h2735, h3082, hlam]
                            · linarith only [h0, h3082, hlam]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h0, h2735, hc01, hc23, hlam, hphi, ht12, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h1894, h2735, hc01, hc23, hlam, hphi, ht12, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2052, h2735, hc01, hc23, hlam, hphi, ht12, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h3063, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2982, hlam, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h3061, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h3063, hlam, p3069_1]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          rcases p3069_3 (m.d 0 1) (by simp) with h3094 | h3094
                          · linarith only [h3094, hlam, p3069_0]
                          · rcases p3069_3 (m.d 1 2) (by simp) with h3096 | h3096
                            · linarith only [h2983, h3096, hlam]
                            · linarith only [h0, h3096, hlam]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h2982, h3065, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3069_1, u3ehi3]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h3062, hlam, p3069_0]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [h1894, h2982, h2983, h3063, h3065, h3066, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p3069_1, u3ehi3]
                        · have p3069_0 := h3069c.1
                          have p3069_1 := h3069c.2.1
                          have p3069_2 := h3069c.2.2.1
                          have p3069_3 := h3069c.2.2.2
                          linarith only [hlam, p3069_0]
                    · linarith only [h1769, h2734, h2735, h3066, hlam]
                  · linarith only [h1769, h2734, h2735, h3065, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1769, h2734, h3062, hlam]
            · linarith only [h1769, h2734, h3061, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3107 | h3107
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3108 | h3108
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3109 | h3109
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3110 | h3110
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3111 | h3111
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3112 | h3112
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3113 | h3113
                      · rcases h1bigk with h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h0, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h1769, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h1894, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2052, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2982, h3111, hc01, hc23, hlam, hphi, ht12, p3114_1]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2735, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2982, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2052, h2982, h3111, hc01, hc23, hlam, hphi, ht12, p3114_1]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          rcases p3114_3 (m.d 0 1) (by simp) with h3125 | h3125
                          · linarith only [h3125, hlam, p3114_0]
                          · rcases p3114_3 (m.d 1 2) (by simp) with h3127 | h3127
                            · linarith only [h2735, h3127, hlam]
                            · linarith only [h0, h3127, hlam]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h3107, h3112, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3114_1, u3ehi4]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2735, h2982, h3107, h3112, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3114_1, u3ehi4]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2052, h2735, hc01, hc23, hlam, hphi, ht12, p3114_1]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          rcases p3114_3 (m.d 0 1) (by simp) with h3134 | h3134
                          · linarith only [h3134, hlam, p3114_0]
                          · rcases p3114_3 (m.d 1 2) (by simp) with h3136 | h3136
                            · linarith only [h2982, h3136, hlam]
                            · linarith only [h0, h3136, hlam]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h3107, h3112, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3114_1, u3ehi4]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h3108, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2052, h2735, h3108, hc01, hc23, hlam, hphi, ht12, p3114_1]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h2735, h3107, hc01, hc23, hlam, hphi, ht12, p3114_1]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h3107, hlam, p3114_1]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h3109, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [h3110, hlam, p3114_0]
                        · have p3114_0 := h3114c.1
                          have p3114_1 := h3114c.2.1
                          have p3114_2 := h3114c.2.2.1
                          have p3114_3 := h3114c.2.2.2
                          linarith only [hlam, p3114_0]
                      · rcases h1bigk with h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c | h3148c
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h0, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h1769, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h1894, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2052, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2982, h3111, hc01, hc23, hlam, hphi, ht12, p3148_1]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2735, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2982, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2052, h2982, h3111, hc01, hc23, hlam, hphi, ht12, p3148_1]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          rcases p3148_3 (m.d 0 1) (by simp) with h3159 | h3159
                          · linarith only [h3159, hlam, p3148_0]
                          · rcases p3148_3 (m.d 1 2) (by simp) with h3161 | h3161
                            · linarith only [h2735, h3161, hlam]
                            · linarith only [h0, h3161, hlam]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h0, h2735, hc01, hc23, hlam, hphi, ht12, p3148_1]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h1894, h2735, hc01, hc23, hlam, hphi, ht12, p3148_1]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2735, h3110, h3113, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3148_1, u3ehi3]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          rcases p3148_3 (m.d 0 1) (by simp) with h3168 | h3168
                          · linarith only [h3168, hlam, p3148_0]
                          · rcases p3148_3 (m.d 1 2) (by simp) with h3170 | h3170
                            · linarith only [h2982, h3170, hlam]
                            · linarith only [h0, h3170, hlam]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h3107, h3112, h3113, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3148_1, u3ehi3]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h3108, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2982, h3110, h3111, h3113, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3148_1, u3ehi3]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h2735, h3107, hc01, hc23, hlam, hphi, ht12, p3148_1]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h3107, hlam, p3148_1]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h3109, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [h3110, hlam, p3148_0]
                        · have p3148_0 := h3148c.1
                          have p3148_1 := h3148c.2.1
                          have p3148_2 := h3148c.2.2.1
                          have p3148_3 := h3148c.2.2.2
                          linarith only [hlam, p3148_0]
                    · linarith only [h0, h2982, h3111, h3112, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1769, h2733, h2735, h3111, hlam]
                · linarith only [h2982, h3107, h3110, hlam]
              · linarith only [h1769, h2734, h3109, hlam]
            · linarith only [h1769, h2733, h3108, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3187 | h3187
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3188 | h3188
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3189 | h3189
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3190 | h3190
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3191 | h3191
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3192 | h3192
                      · rcases h1bigk with h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h1769, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h1894, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h2052, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h2982, h3190, hc01, hc23, hlam, hphi, ht12, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h2735, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h2982, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h3107, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          rcases p3193_3 (m.d 0 1) (by simp) with h3204 | h3204
                          · linarith only [h3204, hlam, p3193_0]
                          · rcases p3193_3 (m.d 1 2) (by simp) with h3206 | h3206
                            · linarith only [h2735, h3206, hlam]
                            · linarith only [h0, h3206, hlam]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, hc01, hc13, hlam, hphi, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, h2735, h3107, h3189, hc01, hc23, hlam, hphi, ht12, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, h2735, h3107, hc01, hc23, hlam, hphi, ht12, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          rcases p3193_3 (m.d 0 1) (by simp) with h3213 | h3213
                          · linarith only [h3213, hlam, p3193_0]
                          · rcases p3193_3 (m.d 1 2) (by simp) with h3215 | h3215
                            · linarith only [h2982, h3215, hlam]
                            · linarith only [h0, h3215, hlam]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h3187, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, h2982, h3107, h3190, hc01, hc23, hlam, hphi, ht12, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          rcases p3193_3 (m.d 0 1) (by simp) with h3222 | h3222
                          · linarith only [h3222, hlam, p3193_0]
                          · rcases p3193_3 (m.d 1 2) (by simp) with h3224 | h3224
                            · linarith only [h3107, h3224, hlam]
                            · linarith only [h0, h3224, hlam]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p3193_1]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h3188, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [h3189, hlam, p3193_0]
                        · have p3193_0 := h3193c.1
                          have p3193_1 := h3193c.2.1
                          have p3193_2 := h3193c.2.2.1
                          have p3193_3 := h3193c.2.2.2
                          linarith only [hlam, p3193_0]
                      · rcases h1bigk with h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c | h3231c
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h0, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h1769, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h1894, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h2052, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h2735, hc01, hc23, hlam, hphi, ht12, p3231_1]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h2735, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h2982, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h3107, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          rcases p3231_3 (m.d 0 1) (by simp) with h3242 | h3242
                          · linarith only [h3242, hlam, p3231_0]
                          · rcases p3231_3 (m.d 1 2) (by simp) with h3244 | h3244
                            · linarith only [h2735, h3244, hlam]
                            · linarith only [h0, h3244, hlam]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h0, h2735, hc01, hc23, hlam, hphi, ht12, p3231_1]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h1894, h2735, hc01, hc23, hlam, hphi, ht12, p3231_1]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h0, h2735, h3107, hc01, hc23, hlam, hphi, ht12, p3231_1]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          rcases p3231_3 (m.d 0 1) (by simp) with h3251 | h3251
                          · linarith only [h3251, hlam, p3231_0]
                          · rcases p3231_3 (m.d 1 2) (by simp) with h3253 | h3253
                            · linarith only [h2982, h3253, hlam]
                            · linarith only [h0, h3253, hlam]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p3231_1]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h3187, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h2982, h3189, h3190, h3192, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3231_1, u3ehi3]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          rcases p3231_3 (m.d 0 1) (by simp) with h3260 | h3260
                          · linarith only [h3260, hlam, p3231_0]
                          · rcases p3231_3 (m.d 1 2) (by simp) with h3262 | h3262
                            · linarith only [h3107, h3262, hlam]
                            · linarith only [h0, h3262, hlam]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p3231_1]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h3188, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [h3189, hlam, p3231_0]
                        · have p3231_0 := h3231c.1
                          have p3231_1 := h3231c.2.1
                          have p3231_2 := h3231c.2.2.1
                          have p3231_3 := h3231c.2.2.2
                          linarith only [hlam, p3231_0]
                    · linarith only [h1769, h2733, h2735, h3191, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1769, h2734, h2735, h3190, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3271 | h3271
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3272 | h3272
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3273 | h3273
                      · linarith only [h1894, h2733, h3189, h3273, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h0, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h1769, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h1894, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h2052, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h2982, hc01, hc24, hlam, hphi, ht12, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h2735, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h2982, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h3107, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          rcases p3275_3 (m.d 0 1) (by simp) with h3286 | h3286
                          · linarith only [h3286, hlam, p3275_0]
                          · rcases p3275_3 (m.d 1 2) (by simp) with h3288 | h3288
                            · linarith only [h2735, h3288, hlam]
                            · linarith only [h0, h3288, hlam]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h0, h2735, hc01, hc23, hlam, hphi, ht12, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h1894, h2735, hc01, hc23, hlam, hphi, ht12, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h2052, h2735, hc01, hc23, hlam, hphi, ht12, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h3189, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h3187, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h3189, hlam, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          rcases p3275_3 (m.d 0 1) (by simp) with h3300 | h3300
                          · linarith only [h3300, hlam, p3275_0]
                          · rcases p3275_3 (m.d 1 2) (by simp) with h3302 | h3302
                            · linarith only [h3107, h3302, hlam]
                            · linarith only [h0, h3302, hlam]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p3275_1]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h3188, hlam, p3275_0]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [h1894, h2733, h3189, hc45, hlam, hphi, ht34, p3275_1, u3ehi3]
                        · have p3275_0 := h3275c.1
                          have p3275_1 := h3275c.2.1
                          have p3275_2 := h3275c.2.2.1
                          have p3275_3 := h3275c.2.2.2
                          linarith only [hlam, p3275_0]
                    · linarith only [h1769, h2734, h2735, h3272, hlam]
                  · linarith only [h1769, h2734, h2735, h3271, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1769, h2734, h3188, hlam]
            · linarith only [h1769, h2733, h3187, hlam]
    · linarith only [h2733, h2734, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3314 | h3314
    · linarith only [h2733, h3314, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3316 | h3316
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3317 | h3317
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3318 | h3318
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3319 | h3319
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3320 | h3320
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3321 | h3321
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3322 | h3322
                  · linarith only [h2733, h3316, h3322, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h0, h2147, h3319, h3322, hc01, hc13, hlam, hphi]
                · linarith only [h2733, h3319, h3321, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2733, h3319, h3320, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3327 | h3327
              · linarith only [h3319, h3327, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3329 | h3329
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3330 | h3330
                  · linarith only [h1769, h3319, h3330, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3332 | h3332
                    · linarith only [h3316, h3327, h3332, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3334 | h3334
                      · rcases h1bigk with h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h0, hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h1769, hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h1894, hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h2052, hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          rcases p3335_3 (m.d 0 1) (by simp) with h3341 | h3341
                          · linarith only [h3341, hlam, p3335_0]
                          · rcases p3335_3 (m.d 1 2) (by simp) with h3343 | h3343
                            · rcases p3335_3 (m.d 1 3) (by simp) with h3344 | h3344
                              · linarith only [h3316, h3344, hlam]
                              · linarith only [h1769, h3344, hlam]
                            · linarith only [h3343, hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h0, h2147, h3316, hc01, hc12, hlam, hphi, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3327, h3334, hc01, hc34, hlam, hphi, ht12, ht23, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3316, hlam, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3319, hlam, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3327, hlam, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          rcases p3335_3 (m.d 0 1) (by simp) with h3357 | h3357
                          · linarith only [h3357, hlam, p3335_0]
                          · rcases p3335_3 (m.d 1 2) (by simp) with h3359 | h3359
                            · rcases p3335_3 (m.d 1 3) (by simp) with h3360 | h3360
                              · linarith only [h3319, h3360, hlam]
                              · linarith only [h1769, h3360, hlam]
                            · linarith only [h0, h3359, hlam]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3317, hlam, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h0, h2147, h3316, hc01, hc14, hlam, hphi, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h0, h2147, h3316, h3319, h3327, hc01, hc34, hlam, hphi, ht12, ht23, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          rcases p3335_3 (m.d 0 1) (by simp) with h3368 | h3368
                          · linarith only [h3368, hlam, p3335_0]
                          · rcases p3335_3 (m.d 1 2) (by simp) with h3370 | h3370
                            · rcases p3335_3 (m.d 1 3) (by simp) with h3371 | h3371
                              · linarith only [h3327, h3371, hlam]
                              · linarith only [h1769, h3371, hlam]
                            · linarith only [h0, h3370, hlam]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3318, hlam, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h0, h2147, h3316, hc01, hc15, hlam, hphi, p3335_1]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [h3329, hlam, p3335_0]
                        · have p3335_0 := h3335c.1
                          have p3335_1 := h3335c.2.1
                          have p3335_2 := h3335c.2.2.1
                          have p3335_3 := h3335c.2.2.2
                          linarith only [hlam, p3335_0]
                      · linarith only [h3319, h3329, h3334, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3380 | h3380
                  · linarith only [h2733, h3316, h3380, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3382 | h3382
                    · linarith only [h3316, h3319, h3329, h3382, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3384 | h3384
                      · linarith only [h0, h2147, h3316, h3319, h3329, h3384, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2733, h3384, hc45, hlam, hphi, ht34, u3ehi0]
          · linarith only [h0, h2147, h3316, h3318, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h2147, h3316, h3317, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3389 | h3389
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3390 | h3390
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3391 | h3391
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3392 | h3392
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3393 | h3393
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3394 | h3394
                  · linarith only [h2733, h3316, h3389, h3394, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h3316, h3389, h3391, h3394, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h2733, h3391, h3393, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2733, h3316, h3389, h3391, h3392, hc35, hlam, hphi, u3ehi0]
            · linarith only [h3316, h3389, h3391, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3400 | h3400
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3401 | h3401
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3402 | h3402
                · linarith only [h3389, h3390, h3402, hlam]
                · linarith only [h2733, h3400, h3402, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2733, h3400, h3401, hc35, hlam, hphi, u3ehi0]
            · linarith only [h3316, h3389, h3400, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3407 | h3407
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3408 | h3408
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3409 | h3409
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3410 | h3410
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3411 | h3411
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3412 | h3412
                    · linarith only [h3314, h3389, h3407, h3411, h3412, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h3389, h3411, h3412, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h3316, h3408, h3411, hlam]
                · linarith only [h2733, h3408, h3410, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2733, h3408, h3409, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3418 | h3418
              · linarith only [h3408, h3418, hc34, hlam, hphi, u3ehi4]
              · linarith only [h3316, h3407, h3418, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3421 | h3421
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3422 | h3422
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3423 | h3423
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3424 | h3424
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3425 | h3425
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3426 | h3426
                      · rcases h1bigk with h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h0, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h1769, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h1894, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h2052, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3389, h3424, hc01, hc23, hlam, hphi, ht12, p3427_1]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3316, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3389, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3407, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          rcases p3427_3 (m.d 0 1) (by simp) with h3438 | h3438
                          · linarith only [h3438, hlam, p3427_0]
                          · rcases p3427_3 (m.d 1 2) (by simp) with h3440 | h3440
                            · linarith only [h3316, h3440, hlam]
                            · linarith only [h0, h3440, hlam]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h0, hc01, hc13, hlam, hphi, p3427_1]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h1894, h3316, hc01, hc23, hlam, hphi, ht12, p3427_1]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h0, h3316, h3407, hc01, hc23, hlam, hphi, ht12, p3427_1]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          rcases p3427_3 (m.d 0 1) (by simp) with h3447 | h3447
                          · linarith only [h3447, hlam, p3427_0]
                          · rcases p3427_3 (m.d 1 2) (by simp) with h3449 | h3449
                            · linarith only [h3389, h3449, hlam]
                            · linarith only [h0, h3449, hlam]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p3427_1]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3421, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3314, h3389, h3422, h3424, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3427_1, u3ehi0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          rcases p3427_3 (m.d 0 1) (by simp) with h3456 | h3456
                          · linarith only [h3456, hlam, p3427_0]
                          · rcases p3427_3 (m.d 1 2) (by simp) with h3458 | h3458
                            · linarith only [h3407, h3458, hlam]
                            · linarith only [h0, h3458, hlam]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p3427_1]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3422, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [h3423, hlam, p3427_0]
                        · have p3427_0 := h3427c.1
                          have p3427_1 := h3427c.2.1
                          have p3427_2 := h3427c.2.2.1
                          have p3427_3 := h3427c.2.2.2
                          linarith only [hlam, p3427_0]
                      · linarith only [h2733, h3426, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h0, h3316, h3425, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h3316, h3421, h3424, hlam]
                · linarith only [h2733, h3421, h3423, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2733, h3421, h3422, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3470 | h3470
              · linarith only [h3421, h3470, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3472 | h3472
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3473 | h3473
                  · linarith only [h1769, h3421, h3473, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3316, h3473, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3476 | h3476
                  · linarith only [h0, h3316, h3421, h3476, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3316, h3476, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1894 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2052 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2147 | h2147
  · exact r1l7_11_23_L_I_M_IR_x1_x1_x1_x1_x0 m hb1 hb3 h0 h1769 h1894 h2052 h2147
  · exact r1l7_11_23_L_I_M_IR_x1_x1_x1_x1_x1 m hb1 hb3 h0 h1769 h1894 h2052 h2147

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1894 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2052 | h2052
  · exact r1l7_11_23_L_I_M_IR_x1_x1_x1_x0 m hb1 hb3 h0 h1769 h1894 h2052
  · exact r1l7_11_23_L_I_M_IR_x1_x1_x1_x1 m hb1 hb3 h0 h1769 h1894 h2052

end R2N4
