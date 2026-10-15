import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S15
import Jsp000404.R1LeavesN7_41S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1842 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2003 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2071 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2765 | h2765
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2766 | h2766
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2767 | h2767
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2768 | h2768
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2769 | h2769
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2770 | h2770
            · linarith only [h2071, h2766, h2770, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2772 | h2772
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2773 | h2773
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2774 | h2774
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2775 | h2775
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2776 | h2776
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2777 | h2777
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2778 | h2778
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2779 | h2779
                            · linarith only [h0, h2765, h2770, h2779, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h1842, h2769, h2770, h2772, h2777, h2779, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h2766, h2770, h2778, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h1842, h2767, h2769, h2770, h2772, h2777, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h1842, h2769, h2776, hlam]
                    · linarith only [h1652, h2071, h2765, h2768, h2769, h2775, hlam]
                  · linarith only [h1652, h2767, h2774, hlam]
                · linarith only [h0, h2766, h2773, hlam]
              · linarith only [h0, h2765, h2772, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2789 | h2789
            · linarith only [h2071, h2766, h2789, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2791 | h2791
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2792 | h2792
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2793 | h2793
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2794 | h2794
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2795 | h2795
                      · linarith only [h1842, h2769, h2789, h2791, h2795, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2797 | h2797
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2798 | h2798
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2799 | h2799
                            · linarith only [h0, h2765, h2789, h2799, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2801 | h2801
                              · linarith only [h0, h1842, h2766, h2789, h2795, h2797, h2799, h2801, hc01, hc23, hlam, hphi, ht12]
                              · rcases h1bigk with h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h0, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1652, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1842, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2003, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2789, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2789, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1842, h2789, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1842, h2789, h2795, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  rcases p2803_3 (m.d 0 1) (by simp) with h2814 | h2814
                                  · linarith only [h2814, hlam, p2803_0]
                                  · rcases p2803_3 (m.d 1 2) (by simp) with h2816 | h2816
                                    · linarith only [h2789, h2816, hlam]
                                    · linarith only [h0, h2816, hlam]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h0, h2766, hc13, hlam, hphi, ht01, ht0b, ht5b, p2803_1, u5ehi2]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1842, h2789, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1842, h2789, h2795, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2795, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2791, hlam, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2793, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2795, hlam, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2789, h2792, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2792, hlam, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h2794, hlam, p2803_0]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [h1842, h2789, h2792, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                · have p2803_0 := h2803c.1
                                  have p2803_1 := h2803c.2.1
                                  have p2803_2 := h2803c.2.2.1
                                  have p2803_3 := h2803c.2.2.2
                                  linarith only [hlam, p2803_0]
                          · linarith only [h0, h2766, h2789, h2798, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h2766, h2767, h2789, h2797, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · linarith only [h1652, h2071, h2766, h2768, h2794, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1652, h2767, h2793, hlam]
                · linarith only [h0, h2766, h2792, hlam]
              · linarith only [h0, h2765, h2791, hlam]
        · linarith only [h2767, h2768, hc35, hlam, hphi, u3ehi3]
      · linarith only [h2071, h2765, h2767, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2841 | h2841
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2842 | h2842
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2843 | h2843
          · linarith only [h2765, h2766, h2843, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2845 | h2845
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2846 | h2846
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2847 | h2847
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2848 | h2848
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2849 | h2849
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2850 | h2850
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2851 | h2851
                        · linarith only [h2071, h2765, h2845, h2851, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h2071, h2841, h2843, h2848, h2850, h2851, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2854 | h2854
                        · linarith only [h2071, h2765, h2845, h2854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h2071, h2765, h2841, h2854, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1652, h2841, h2849, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1652, h2765, h2766, h2841, h2848, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h2071, h2845, h2847, hc02, hc25, hlam, hphi]
              · linarith only [h2071, h2765, h2841, h2845, h2846, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2861 | h2861
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2862 | h2862
                · linarith only [h2765, h2766, h2841, h2845, h2862, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2864 | h2864
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2865 | h2865
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2866 | h2866
                      · linarith only [h2841, h2843, h2845, h2861, h2866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2868 | h2868
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2869 | h2869
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2870 | h2870
                            · linarith only [h0, h2765, h2862, h2866, h2869, h2870, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h2765, h2862, h2868, h2870, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h2071, h2765, h2868, h2869, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h2845, h2868, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1652, h2842, h2865, hlam]
                  · linarith only [h0, h1652, h2765, h2841, h2862, h2864, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h2765, h2861, hlam]
        · linarith only [h2841, h2842, hc35, hlam, hphi, u3ehi3]
      · linarith only [h2071, h2765, h2841, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2880 | h2880
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2881 | h2881
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2882 | h2882
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2883 | h2883
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2884 | h2884
            · linarith only [h2071, h2880, h2884, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2886 | h2886
              · linarith only [h2765, h2880, h2886, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2888 | h2888
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2889 | h2889
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2890 | h2890
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2891 | h2891
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2892 | h2892
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2893 | h2893
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2894 | h2894
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2895 | h2895
                              · rcases h1bigk with h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c | h2896c
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h0, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h1652, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h1842, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2003, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2886, h2892, hc01, hc23, hlam, hphi, ht12, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2884, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2886, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2003, h2886, h2892, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2896_1, u5ehi0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  rcases p2896_3 (m.d 0 1) (by simp) with h2907 | h2907
                                  · linarith only [h2907, hlam, p2896_0]
                                  · rcases p2896_3 (m.d 1 2) (by simp) with h2909 | h2909
                                    · linarith only [h2884, h2909, hlam]
                                    · linarith only [h0, h2909, hlam]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h0, hc01, hc13, hlam, hphi, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h1842, hc01, hc13, hlam, hphi, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2003, h2884, hc01, hc23, hlam, hphi, ht12, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  rcases p2896_3 (m.d 0 1) (by simp) with h2916 | h2916
                                  · linarith only [h2916, hlam, p2896_0]
                                  · rcases p2896_3 (m.d 1 2) (by simp) with h2918 | h2918
                                    · linarith only [h2886, h2918, hlam]
                                    · linarith only [h0, h2918, hlam]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h0, h2880, h2893, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2896_1, u3ehi4]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2889, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2003, h2886, h2892, hc01, hc23, hlam, hphi, ht12, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2884, h2888, hc01, hc23, hlam, hphi, ht12, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2888, hlam, p2896_1]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2890, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [h2891, hlam, p2896_0]
                                · have p2896_0 := h2896c.1
                                  have p2896_1 := h2896c.2.1
                                  have p2896_2 := h2896c.2.2.1
                                  have p2896_3 := h2896c.2.2.2
                                  linarith only [hlam, p2896_0]
                              · linarith only [h0, h2880, h2886, h2892, h2894, h2895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h2880, h2886, h2894, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                          · linarith only [h0, h2880, h2886, h2892, h2893, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h2880, h2884, h2892, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h1652, h1842, h2881, h2883, h2891, hc01, hc13, hlam, hphi]
                    · linarith only [h1652, h2003, h2881, h2882, h2883, h2884, h2888, h2890, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h2880, h2881, h2884, h2889, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h2880, h2888, hlam]
          · linarith only [h2765, h2880, h2883, hlam]
        · linarith only [h2881, h2882, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2940 | h2940
        · linarith only [h2881, h2940, hc34, hlam, hphi, u3ehi4]
        · linarith only [h2071, h2880, h2940, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2943 | h2943
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2944 | h2944
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2945 | h2945
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2946 | h2946
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2947 | h2947
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2948 | h2948
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2949 | h2949
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2950 | h2950
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2951 | h2951
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2952 | h2952
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2953 | h2953
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2954 | h2954
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2955 | h2955
                              · linarith only [h2071, h2943, h2946, h2955, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h2765, h2945, h2946, h2952, h2955, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h2765, h2945, h2954, hlam]
                          · linarith only [h2071, h2943, h2953, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h2071, h2943, h2952, hlam]
                      · linarith only [h1842, h2765, h2945, h2951, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h2071, h2944, h2946, h2950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h2071, h2943, h2946, h2949, hlam]
                · linarith only [h2071, h2946, h2948, hc02, hc25, hlam, hphi]
              · linarith only [h2071, h2943, h2946, h2947, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2966 | h2966
              · linarith only [h2765, h2946, h2966, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2968 | h2968
                · linarith only [h0, h2880, h2946, h2968, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2970 | h2970
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2971 | h2971
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2972 | h2972
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2973 | h2973
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2974 | h2974
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2975 | h2975
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2976 | h2976
                              · rcases h1bigk with h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h1652, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h1842, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2003, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2968, h2973, h2975, hc01, hc23, hlam, hphi, ht12, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2946, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2966, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2968, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  rcases p2977_3 (m.d 0 1) (by simp) with h2988 | h2988
                                  · linarith only [h2988, hlam, p2977_0]
                                  · rcases p2977_3 (m.d 1 2) (by simp) with h2990 | h2990
                                    · linarith only [h2946, h2990, hlam]
                                    · linarith only [h0, h2990, hlam]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, hc01, hc13, hlam, hphi, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h1842, h2943, h2946, h2976, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2977_1, u5ehi4]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, h2946, h2968, hc01, hc23, hlam, hphi, ht12, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  rcases p2977_3 (m.d 0 1) (by simp) with h2997 | h2997
                                  · linarith only [h2997, hlam, p2977_0]
                                  · rcases p2977_3 (m.d 1 2) (by simp) with h2999 | h2999
                                    · linarith only [h2966, h2999, hlam]
                                    · linarith only [h0, h2999, hlam]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2970, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, h2966, h2968, h2973, hc01, hc23, hlam, hphi, ht12, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  rcases p2977_3 (m.d 0 1) (by simp) with h3006 | h3006
                                  · linarith only [h3006, hlam, p2977_0]
                                  · rcases p2977_3 (m.d 1 2) (by simp) with h3008 | h3008
                                    · linarith only [h2968, h3008, hlam]
                                    · linarith only [h0, h3008, hlam]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2971, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2972, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                              · rcases h1bigk with h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c | h3015c
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h0, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h1652, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h1842, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2003, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2946, hc01, hc23, hlam, hphi, ht12, p3015_1]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2946, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2966, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2968, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  rcases p3015_3 (m.d 0 1) (by simp) with h3026 | h3026
                                  · linarith only [h3026, hlam, p3015_0]
                                  · rcases p3015_3 (m.d 1 2) (by simp) with h3028 | h3028
                                    · linarith only [h2946, h3028, hlam]
                                    · linarith only [h0, h3028, hlam]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h0, h2946, hc01, hc23, hlam, hphi, ht12, p3015_1]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h1842, h2945, h2946, h2976, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3015_1]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2003, h2946, hc01, hc23, hlam, hphi, ht12, p3015_1]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  rcases p3015_3 (m.d 0 1) (by simp) with h3035 | h3035
                                  · linarith only [h3035, hlam, p3015_0]
                                  · rcases p3015_3 (m.d 1 2) (by simp) with h3037 | h3037
                                    · linarith only [h2966, h3037, hlam]
                                    · linarith only [h0, h3037, hlam]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p3015_1]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2970, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2003, h2945, h2966, h2973, h2976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3015_1, u3ehi3]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  rcases p3015_3 (m.d 0 1) (by simp) with h3044 | h3044
                                  · linarith only [h3044, hlam, p3015_0]
                                  · rcases p3015_3 (m.d 1 2) (by simp) with h3046 | h3046
                                    · linarith only [h2968, h3046, hlam]
                                    · linarith only [h0, h3046, hlam]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p3015_1]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2971, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [h2972, hlam, p3015_0]
                                · have p3015_0 := h3015c.1
                                  have p3015_1 := h3015c.2.1
                                  have p3015_2 := h3015c.2.2.1
                                  have p3015_3 := h3015c.2.2.2
                                  linarith only [hlam, p3015_0]
                            · linarith only [h1652, h1842, h2943, h2945, h2946, h2966, h2975, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h1652, h2943, h2946, h2974, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1652, h2943, h2946, h2973, hlam]
                      · linarith only [h1842, h2945, h2972, hlam]
                    · linarith only [h1652, h2943, h2971, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1652, h2943, h2970, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3059 | h3059
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3060 | h3060
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3061 | h3061
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3062 | h3062
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3063 | h3063
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3064 | h3064
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3065 | h3065
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3066 | h3066
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3067 | h3067
                            · linarith only [h2943, h2945, h3059, h3065, h3067, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h2765, h3059, h3062, h3064, h3067, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h1652, h2071, h2944, h3059, h3066, hc01, hc12, hlam, hphi]
                        · linarith only [h2071, h2944, h3065, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3072 | h3072
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3073 | h3073
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3074 | h3074
                            · linarith only [h1842, h3064, h3074, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3076 | h3076
                              · linarith only [h0, h2765, h2943, h3060, h3064, h3076, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h1bigk with h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h0, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h1652, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h1842, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h2003, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  rcases p3078_3 (m.d 0 1) (by simp) with h3084 | h3084
                                  · linarith only [h3084, hlam, p3078_0]
                                  · rcases p3078_3 (m.d 1 2) (by simp) with h3086 | h3086
                                    · rcases p3078_3 (m.d 1 3) (by simp) with h3087 | h3087
                                      · linarith only [h3059, h3087, hlam]
                                      · linarith only [h1652, h3087, hlam]
                                    · linarith only [h3086, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h1652, hc01, hc12, hlam, hphi, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h0, h2765, h3060, hc01, hc12, hlam, hphi, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h2003, hc01, hc12, hlam, hphi, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  rcases p3078_3 (m.d 0 1) (by simp) with h3095 | h3095
                                  · linarith only [h3095, hlam, p3078_0]
                                  · rcases p3078_3 (m.d 1 2) (by simp) with h3097 | h3097
                                    · rcases p3078_3 (m.d 1 3) (by simp) with h3098 | h3098
                                      · rcases p3078_3 (m.d 1 4) (by simp) with h3099 | h3099
                                        · linarith only [h3062, h3099, hlam]
                                        · linarith only [h1842, h3099, hlam]
                                      · linarith only [h3098, hlam, p3078_0]
                                    · linarith only [h0, h3097, hlam]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3059, hlam, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h0, h2765, h3060, hc01, hc13, hlam, hphi, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h2003, h3059, hc01, hc12, hlam, hphi, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3064, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3060, hlam, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3062, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3064, hlam, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  rcases p3078_3 (m.d 0 1) (by simp) with h3113 | h3113
                                  · linarith only [h3113, hlam, p3078_0]
                                  · rcases p3078_3 (m.d 1 2) (by simp) with h3115 | h3115
                                    · rcases p3078_3 (m.d 1 3) (by simp) with h3116 | h3116
                                      · rcases p3078_3 (m.d 1 4) (by simp) with h3117 | h3117
                                        · linarith only [h3064, h3117, hlam]
                                        · linarith only [h1842, h3117, hlam]
                                      · linarith only [h1652, h3116, hlam]
                                    · linarith only [h0, h3115, hlam]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3061, hlam, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h3063, hlam, p3078_0]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [h1842, hc01, hc15, hlam, hphi, p3078_1]
                                · have p3078_0 := h3078c.1
                                  have p3078_1 := h3078c.2.1
                                  have p3078_2 := h3078c.2.2.1
                                  have p3078_3 := h3078c.2.2.2
                                  linarith only [hlam, p3078_0]
                          · linarith only [h2071, h2944, h3073, hlam]
                        · linarith only [h2071, h2944, h3072, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h2071, h2944, h3059, h3063, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h2071, h2943, h3059, h3062, hlam]
                · linarith only [h2071, h2944, h3059, h3061, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h2071, h2943, h3059, h3060, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3132 | h3132
              · linarith only [h0, h2765, h3059, h3132, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3134 | h3134
                · linarith only [h0, h2880, h3059, h3134, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3136 | h3136
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3137 | h3137
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3138 | h3138
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3139 | h3139
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3140 | h3140
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3141 | h3141
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3142 | h3142
                              · linarith only [h2943, h2945, h3142, hlam]
                              · rcases h1bigk with h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h0, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h1652, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h1842, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h2003, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3134, h3139, h3141, hc01, hc23, hlam, hphi, ht12, p3144_1]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3059, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3132, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3134, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  rcases p3144_3 (m.d 0 1) (by simp) with h3155 | h3155
                                  · linarith only [h3155, hlam, p3144_0]
                                  · rcases p3144_3 (m.d 1 2) (by simp) with h3157 | h3157
                                    · linarith only [h3059, h3157, hlam]
                                    · linarith only [h0, h3157, hlam]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h0, hc01, hc13, hlam, hphi, p3144_1]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h2943, h2945, h3059, h3138, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3144_1, u3ehi3]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h2003, h3059, hc01, hc23, hlam, hphi, ht12, p3144_1]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  rcases p3144_3 (m.d 0 1) (by simp) with h3164 | h3164
                                  · linarith only [h3164, hlam, p3144_0]
                                  · rcases p3144_3 (m.d 1 2) (by simp) with h3166 | h3166
                                    · linarith only [h3132, h3166, hlam]
                                    · linarith only [h0, h3166, hlam]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p3144_1]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3136, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h2943, h2945, h3132, h3138, h3139, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3144_1, u3ehi3]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  rcases p3144_3 (m.d 0 1) (by simp) with h3173 | h3173
                                  · linarith only [h3173, hlam, p3144_0]
                                  · rcases p3144_3 (m.d 1 2) (by simp) with h3175 | h3175
                                    · linarith only [h3134, h3175, hlam]
                                    · linarith only [h0, h3175, hlam]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p3144_1]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3137, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [h3138, hlam, p3144_0]
                                · have p3144_0 := h3144c.1
                                  have p3144_1 := h3144c.2.1
                                  have p3144_2 := h3144c.2.2.1
                                  have p3144_3 := h3144c.2.2.2
                                  linarith only [hlam, p3144_0]
                            · linarith only [h0, h3132, h3141, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h1652, h2943, h3059, h3140, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h2943, h2945, h3059, h3136, h3138, h3139, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3185 | h3185
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3186 | h3186
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3187 | h3187
                            · linarith only [h1842, h3138, h3187, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h3132, h3187, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h1652, h2944, h3059, h3186, hlam]
                        · linarith only [h1652, h1842, h2943, h3059, h3138, h3185, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h1652, h2944, h3137, hlam]
                  · linarith only [h1652, h2943, h3136, hlam]
        · linarith only [h2943, h2944, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3195 | h3195
        · linarith only [h2943, h3195, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3197 | h3197
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3198 | h3198
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3199 | h3199
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3200 | h3200
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3201 | h3201
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3202 | h3202
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3203 | h3203
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3204 | h3204
                        · linarith only [h2943, h3198, h3204, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h2071, h3198, h3201, h3204, hc01, hc12, hlam, hphi]
                      · linarith only [h1842, h2765, h3197, h3203, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h3201, h3202, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3209 | h3209
                    · linarith only [h3201, h3209, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3211 | h3211
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3212 | h3212
                        · linarith only [h1652, h3201, h3212, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3214 | h3214
                          · linarith only [h3198, h3209, h3214, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3216 | h3216
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3217 | h3217
                              · rcases h1bigk with h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c | h3218c
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h0, hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h1652, hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h1842, hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h2003, hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  rcases p3218_3 (m.d 0 1) (by simp) with h3224 | h3224
                                  · linarith only [h3224, hlam, p3218_0]
                                  · rcases p3218_3 (m.d 1 2) (by simp) with h3226 | h3226
                                    · rcases p3218_3 (m.d 1 3) (by simp) with h3227 | h3227
                                      · linarith only [h3198, h3227, hlam]
                                      · linarith only [h1652, h3227, hlam]
                                    · linarith only [h3226, hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h0, h2071, h3198, hc01, hc12, hlam, hphi, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h2765, h3197, h3199, hc12, hlam, hphi, ht01, ht0b, ht5b, p3218_1, u5ehi4]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h2003, hc01, hc12, hlam, hphi, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3209, h3217, hc01, hc34, hlam, hphi, ht12, ht23, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3198, hlam, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3201, hlam, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3209, hlam, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  rcases p3218_3 (m.d 0 1) (by simp) with h3240 | h3240
                                  · linarith only [h3240, hlam, p3218_0]
                                  · rcases p3218_3 (m.d 1 2) (by simp) with h3242 | h3242
                                    · rcases p3218_3 (m.d 1 3) (by simp) with h3243 | h3243
                                      · linarith only [h3201, h3243, hlam]
                                      · linarith only [h1652, h3243, hlam]
                                    · linarith only [h0, h3242, hlam]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3199, hlam, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h1652, hc01, hc14, hlam, hphi, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h0, h2071, h3198, h3201, h3209, hc01, hc34, hlam, hphi, ht12, ht23, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  rcases p3218_3 (m.d 0 1) (by simp) with h3251 | h3251
                                  · linarith only [h3251, hlam, p3218_0]
                                  · rcases p3218_3 (m.d 1 2) (by simp) with h3253 | h3253
                                    · rcases p3218_3 (m.d 1 3) (by simp) with h3254 | h3254
                                      · linarith only [h3209, h3254, hlam]
                                      · linarith only [h1652, h3254, hlam]
                                    · linarith only [h0, h3253, hlam]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3200, hlam, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h0, h2071, h3198, hc01, hc15, hlam, hphi, p3218_1]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [h3211, hlam, p3218_0]
                                · have p3218_0 := h3218c.1
                                  have p3218_1 := h3218c.2.1
                                  have p3218_2 := h3218c.2.2.1
                                  have p3218_3 := h3218c.2.2.2
                                  linarith only [hlam, p3218_0]
                              · linarith only [h2943, h3197, h3217, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h2765, h3197, h3216, hlam]
                      · linarith only [h1842, h2765, h3197, h3211, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h2765, h3197, h3199, h3200, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h2071, h3198, h3199, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3267 | h3267
              · linarith only [h0, h2765, h3198, h3267, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3269 | h3269
                · linarith only [h0, h2880, h3198, h3269, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3271 | h3271
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3272 | h3272
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3273 | h3273
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3274 | h3274
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3275 | h3275
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3276 | h3276
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3277 | h3277
                              · rcases h1bigk with h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c | h3278c
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h0, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h1652, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h1842, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h2003, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3269, h3274, h3276, hc01, hc23, hlam, hphi, ht12, p3278_1]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3198, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3267, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3269, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  rcases p3278_3 (m.d 0 1) (by simp) with h3289 | h3289
                                  · linarith only [h3289, hlam, p3278_0]
                                  · rcases p3278_3 (m.d 1 2) (by simp) with h3291 | h3291
                                    · linarith only [h3198, h3291, hlam]
                                    · linarith only [h0, h3291, hlam]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h0, h3198, hc01, hc23, hlam, hphi, ht12, p3278_1]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h1842, h3198, hc01, hc23, hlam, hphi, ht12, p3278_1]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h2003, h3198, hc01, hc23, hlam, hphi, ht12, p3278_1]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  rcases p3278_3 (m.d 0 1) (by simp) with h3298 | h3298
                                  · linarith only [h3298, hlam, p3278_0]
                                  · rcases p3278_3 (m.d 1 2) (by simp) with h3300 | h3300
                                    · linarith only [h3267, h3300, hlam]
                                    · linarith only [h0, h3300, hlam]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p3278_1]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3271, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3195, h3267, h3272, h3274, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3278_1, u3ehi0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  rcases p3278_3 (m.d 0 1) (by simp) with h3307 | h3307
                                  · linarith only [h3307, hlam, p3278_0]
                                  · rcases p3278_3 (m.d 1 2) (by simp) with h3309 | h3309
                                    · linarith only [h3269, h3309, hlam]
                                    · linarith only [h0, h3309, hlam]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p3278_1]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3272, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [h3273, hlam, p3278_0]
                                · have p3278_0 := h3278c.1
                                  have p3278_1 := h3278c.2.1
                                  have p3278_2 := h3278c.2.2.1
                                  have p3278_3 := h3278c.2.2.2
                                  linarith only [hlam, p3278_0]
                              · linarith only [h2943, h3197, h3277, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1842, h3197, h3267, h3276, hlam]
                          · linarith only [h2943, h3197, h3198, h3271, h3275, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h3198, h3271, h3274, hlam]
                      · linarith only [h1842, h3197, h3273, hlam]
                    · linarith only [h2943, h3271, h3272, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3322 | h3322
                    · linarith only [h3271, h3322, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3324 | h3324
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3325 | h3325
                        · linarith only [h1652, h3271, h3325, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3198, h3325, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1842, h3197, h3324, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3329 | h3329
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3330 | h3330
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3331 | h3331
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3332 | h3332
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3333 | h3333
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3334 | h3334
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3335 | h3335
                        · linarith only [h2943, h3329, h3335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h2071, h3329, h3332, h3335, hc01, hc12, hlam, hphi]
                      · linarith only [h2943, h3332, h3334, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h2943, h3332, h3333, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3340 | h3340
                    · linarith only [h3332, h3340, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3342 | h3342
                      · linarith only [h2943, h3197, h3332, h3342, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3344 | h3344
                        · linarith only [h3329, h3332, h3342, h3344, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3346 | h3346
                          · linarith only [h3329, h3332, h3342, h3346, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3348 | h3348
                            · linarith only [h0, h2071, h3329, h3332, h3342, h3348, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3350 | h3350
                              · linarith only [h0, h2071, h3329, h3332, h3342, h3350, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h2943, h3350, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h0, h2071, h3329, h3331, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h2071, h3329, h3330, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3355 | h3355
              · linarith only [h0, h2765, h3329, h3355, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3357 | h3357
                · linarith only [h0, h2880, h3329, h3357, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3359 | h3359
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3360 | h3360
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3361 | h3361
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3362 | h3362
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3363 | h3363
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3364 | h3364
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3365 | h3365
                              · linarith only [h2943, h3197, h3365, hc34, hlam, hphi, u3ehi0]
                              · linarith only [h2943, h3359, h3361, h3365, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h0, h2765, h3329, h3359, h3361, h3364, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h3329, h3360, h3363, hlam]
                        · linarith only [h3329, h3360, h3362, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h2943, h3359, h3361, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h2943, h3359, h3360, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3373 | h3373
                    · linarith only [h3359, h3373, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3375 | h3375
                      · linarith only [h2943, h3197, h3359, h3375, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3377 | h3377
                        · linarith only [h1652, h3359, h3377, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3329, h3377, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1842 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2003 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2071 | h2071
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1652 h1842 h2003 h2071
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1652 h1842 h2003 h2071

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1842 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2003 | h2003
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1652 h1842 h2003
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1652 h1842 h2003

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1842 | h1842
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x0 m hb1 hb3 hb5 h0 h1652 h1842
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1 m hb1 hb3 hb5 h0 h1652 h1842

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1652 | h1652
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x0 m hb1 hb3 hb5 h0 h1652
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1_x1 m hb1 hb3 hb5 h0 h1652

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x1 m hb1 hb3 hb5 h0

end R2N4
