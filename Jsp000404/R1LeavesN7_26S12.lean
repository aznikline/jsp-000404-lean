import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2761 | h2761
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2762 | h2762
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2763 | h2763
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2764 | h2764
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2765 | h2765
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2766 | h2766
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2767 | h2767
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2768 | h2768
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2769 | h2769
                  · linarith only [h0, h2760, h2769, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2771 | h2771
                    · linarith only [h0, h2760, h2764, h2769, h2771, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2773 | h2773
                      · linarith only [h0, h2761, h2773, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h2761, h2766, h2773, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2760, h2764, h2768, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h2760, h2764, h2766, h2767, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2778 | h2778
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2779 | h2779
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2780 | h2780
                  · linarith only [h0, h2760, h2780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2782 | h2782
                    · linarith only [h0, h2760, h2764, h2780, h2782, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2784 | h2784
                      · linarith only [h0, h2761, h2766, h2784, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2786 | h2786
                        · linarith only [h2778, h2780, h2786, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2788 | h2788
                          · linarith only [h2778, h2782, h2788, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2790 | h2790
                            · linarith only [h0, h2761, h2766, h2779, h2790, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2792 | h2792
                              · linarith only [h2764, h2766, h2792, hlam]
                              · rcases h3bigk with h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c | h2794c
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  rcases p2794_3 (m.d 0 3) (by simp) with h2796 | h2796
                                  · rcases p2794_3 (m.d 1 3) (by simp) with h2797 | h2797
                                    · linarith only [h2760, h2797, hlam]
                                    · rcases p2794_3 (m.d 2 3) (by simp) with h2799 | h2799
                                      · linarith only [h2762, h2799, hlam]
                                      · rcases p2794_3 (m.d 3 4) (by simp) with h2801 | h2801
                                        · linarith only [h2764, h2801, hlam]
                                        · linarith only [h2780, h2801, hlam]
                                  · linarith only [h2760, h2796, hlam]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  rcases p2794_3 (m.d 0 3) (by simp) with h2805 | h2805
                                  · rcases p2794_3 (m.d 1 3) (by simp) with h2806 | h2806
                                    · linarith only [h2760, h2806, hlam]
                                    · linarith only [h2778, h2806, hlam]
                                  · linarith only [h2762, h2805, hlam]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2780, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2778, h2780, h2792, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2760, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2780, hc23, hc34, hlam, hphi, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2780, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2782, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2762, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2778, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2786, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2788, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2764, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2764, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2764, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2792, hlam, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h2765, hlam, p2794_0]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2765, h2778, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2794_1]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [h0, h2760, h2765, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2794_1, u4ehi3]
                                · have p2794_0 := h2794c.1
                                  have p2794_1 := h2794c.2.1
                                  have p2794_2 := h2794c.2.2.1
                                  have p2794_3 := h2794c.2.2.2
                                  linarith only [hlam, p2794_0]
                · linarith only [h0, h2761, h2779, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h2760, h2764, h2778, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2834 | h2834
            · linarith only [h2764, h2765, h2834, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2836 | h2836
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2837 | h2837
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2838 | h2838
                  · linarith only [h0, h2760, h2838, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h2764, h2765, h2836, h2838, hc23, hc35, hlam, hphi]
                · linarith only [h0, h2761, h2837, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h2760, h2764, h2836, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2843 | h2843
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2844 | h2844
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2845 | h2845
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2846 | h2846
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2847 | h2847
                  · linarith only [h0, h2760, h2764, h2847, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2849 | h2849
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2850 | h2850
                      · linarith only [h0, h2761, h2850, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h2761, h2844, h2850, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h2764, h2843, h2849, hc13, hc34, hlam, hphi]
                · linarith only [h0, h2761, h2846, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h2761, h2845, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h2764, h2843, h2844, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2857 | h2857
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2858 | h2858
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2859 | h2859
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2860 | h2860
                  · linarith only [h0, h2760, h2764, h2860, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2862 | h2862
                    · linarith only [h2760, h2843, h2862, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2864 | h2864
                      · linarith only [h0, h2761, h2864, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h2761, h2857, h2864, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2761, h2857, h2859, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h2761, h2857, h2858, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2869 | h2869
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2870 | h2870
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2871 | h2871
                  · linarith only [h0, h2760, h2871, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2873 | h2873
                    · linarith only [h0, h2761, h2843, h2871, h2873, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2875 | h2875
                      · linarith only [h0, h2761, h2875, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2877 | h2877
                        · linarith only [h0, h2760, h2764, h2869, h2877, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2879 | h2879
                          · linarith only [h2760, h2843, h2869, h2879, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2881 | h2881
                            · linarith only [h2763, h2857, h2881, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2883 | h2883
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
                                  linarith only [h2764, h2869, hc23, hc34, hlam, hphi, p2884_1]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2764, hc23, hc34, hlam, hphi, p2884_1]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2764, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2843, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2760, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h0, h2760, h2761, h2857, h2870, h2883, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2884_1, u4ehi2]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2871, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2873, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2762, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2869, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2877, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2879, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  rcases p2884_3 (m.d 0 3) (by simp) with h2900 | h2900
                                  · linarith only [h2900, hlam, p2884_0]
                                  · rcases p2884_3 (m.d 1 3) (by simp) with h2902 | h2902
                                    · linarith only [h2871, h2902, hlam]
                                    · rcases p2884_3 (m.d 2 3) (by simp) with h2904 | h2904
                                      · linarith only [h2877, h2904, hlam]
                                      · rcases p2884_3 (m.d 3 4) (by simp) with h2906 | h2906
                                        · rcases p2884_3 (m.d 3 5) (by simp) with h2907 | h2907
                                          · linarith only [h2883, h2907, hlam]
                                          · linarith only [h2843, h2907, hlam]
                                        · linarith only [h2906, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  rcases p2884_3 (m.d 0 3) (by simp) with h2911 | h2911
                                  · linarith only [h2764, h2911, hlam]
                                  · linarith only [h2760, h2911, hlam]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  rcases p2884_3 (m.d 0 3) (by simp) with h2914 | h2914
                                  · linarith only [h2764, h2914, hlam]
                                  · linarith only [h2762, h2914, hlam]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2761, h2857, h2870, h2883, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2884_1, u4ehi2]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  rcases p2884_3 (m.d 0 3) (by simp) with h2919 | h2919
                                  · linarith only [h2919, hlam, p2884_0]
                                  · rcases p2884_3 (m.d 1 3) (by simp) with h2921 | h2921
                                    · linarith only [h2873, h2921, hlam]
                                    · rcases p2884_3 (m.d 2 3) (by simp) with h2923 | h2923
                                      · linarith only [h2879, h2923, hlam]
                                      · rcases p2884_3 (m.d 3 4) (by simp) with h2925 | h2925
                                        · rcases p2884_3 (m.d 3 5) (by simp) with h2926 | h2926
                                          · rcases h4bigk with h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c | h2927c
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2857, h2870, hc45, hlam, hphi, p2927_1, u4ehi2]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2857, hc45, hlam, hphi, p2927_1, u4ehi2]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2764, hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2857, hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2761, hlam, p2927_1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h0, h2761, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2927_1, u4ehi2]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2871, hlam, p2927_1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2875, hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2763, hlam, p2927_1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2870, hlam, p2927_1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2877, hlam, p2927_1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2881, hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              rcases p2927_3 (m.d 0 4) (by simp) with h2943 | h2943
                                              · linarith only [h2764, h2943, hlam]
                                              · rcases p2927_3 (m.d 1 4) (by simp) with h2945 | h2945
                                                · linarith only [h2871, h2945, hlam]
                                                · rcases p2927_3 (m.d 2 4) (by simp) with h2947 | h2947
                                                  · linarith only [h2877, h2947, hlam]
                                                  · rcases p2927_3 (m.d 3 4) (by simp) with h2949 | h2949
                                                    · rcases p2927_3 (m.d 4 5) (by simp) with h2950 | h2950
                                                      · linarith only [h2883, h2950, hlam]
                                                      · linarith only [h2857, h2950, hlam]
                                                    · linarith only [h2764, h2949, hlam]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              rcases p2927_3 (m.d 0 4) (by simp) with h2954 | h2954
                                              · linarith only [h2764, h2954, hlam]
                                              · linarith only [h2761, h2954, hlam]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              rcases p2927_3 (m.d 0 4) (by simp) with h2957 | h2957
                                              · linarith only [h2764, h2957, hlam]
                                              · linarith only [h2763, h2957, hlam]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2764, h2857, hc03, hc34, hlam, hphi, p2927_1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2761, hc45, hlam, hphi, p2927_1, u4ehi1]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2870, hc45, hlam, hphi, p2927_1, u4ehi2]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [hc45, hlam, hphi, p2927_1, u4ehi2]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [h2883, hlam, p2927_0]
                                            · have p2927_0 := h2927c.1
                                              have p2927_1 := h2927c.2.1
                                              have p2927_2 := h2927c.2.2.1
                                              have p2927_3 := h2927c.2.2.2
                                              linarith only [hlam, p2927_0]
                                          · linarith only [h2926, hlam, p2884_0]
                                        · linarith only [h2764, h2925, hlam]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  rcases p2884_3 (m.d 0 3) (by simp) with h2969 | h2969
                                  · linarith only [h2843, h2969, hlam]
                                  · linarith only [h2760, h2969, hlam]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  rcases p2884_3 (m.d 0 3) (by simp) with h2972 | h2972
                                  · linarith only [h2843, h2972, hlam]
                                  · linarith only [h2762, h2972, hlam]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [h2883, hlam, p2884_0]
                                · have p2884_0 := h2884c.1
                                  have p2884_1 := h2884c.2.1
                                  have p2884_2 := h2884c.2.2.1
                                  have p2884_3 := h2884c.2.2.2
                                  linarith only [hlam, p2884_0]
                              · rcases h3bigk with h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2764, h2869, hc23, hc34, hlam, hphi, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2764, h2883, hc23, hc45, hlam, hphi, ht34, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2764, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2843, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2760, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h0, h2760, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2871, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2873, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2762, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2869, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2877, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2879, hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2883, hc03, hc45, hlam, hphi, ht34, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2883, hc13, hc45, hlam, hphi, ht34, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2883, hc23, hc45, hlam, hphi, ht34, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2883, hlam, p2977_1]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  rcases p2977_3 (m.d 0 3) (by simp) with h2998 | h2998
                                  · linarith only [h2998, hlam, p2977_0]
                                  · rcases p2977_3 (m.d 1 3) (by simp) with h3000 | h3000
                                    · linarith only [h2873, h3000, hlam]
                                    · rcases p2977_3 (m.d 2 3) (by simp) with h3002 | h3002
                                      · linarith only [h2879, h3002, hlam]
                                      · rcases p2977_3 (m.d 3 4) (by simp) with h3004 | h3004
                                        · linarith only [h2883, h3004, hlam]
                                        · linarith only [h2764, h3004, hlam]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  rcases p2977_3 (m.d 0 3) (by simp) with h3007 | h3007
                                  · linarith only [h2843, h3007, hlam]
                                  · linarith only [h2760, h3007, hlam]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  rcases p2977_3 (m.d 0 3) (by simp) with h3010 | h3010
                                  · linarith only [h2843, h3010, hlam]
                                  · linarith only [h2762, h3010, hlam]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [h2883, hc45, hlam, hphi, p2977_1, u4ehi3]
                                · have p2977_0 := h2977c.1
                                  have p2977_1 := h2977c.2.1
                                  have p2977_2 := h2977c.2.2.1
                                  have p2977_3 := h2977c.2.2.2
                                  linarith only [hlam, p2977_0]
                · linarith only [h0, h2761, h2870, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h2761, h2869, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h2761, h2763, hlam]
    · linarith only [h0, h2760, h2762, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3019 | h3019
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3020 | h3020
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3021 | h3021
        · linarith only [h2760, h2761, h3021, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3023 | h3023
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3024 | h3024
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3025 | h3025
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3026 | h3026
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3027 | h3027
                  · linarith only [h2760, h2761, h3021, h3026, h3027, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3029 | h3029
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3030 | h3030
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3031 | h3031
                        · linarith only [h2760, h2761, h3025, h3027, h3031, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3033 | h3033
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3034 | h3034
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3035 | h3035
                              · linarith only [h2760, h2761, h3027, h3029, h3035, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                              · linarith only [h2761, h3020, h3027, h3034, h3035, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · linarith only [h2760, h2761, h3029, h3030, h3034, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h2760, h2761, h3023, h3027, h3033, hc23, hc34, hlam, hphi]
                      · linarith only [h2760, h2761, h3024, h3029, h3030, hc05, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2760, h2761, h3023, h3027, h3029, hc13, hc34, hlam, hphi]
                · linarith only [h0, h3020, h3026, hlam]
              · linarith only [h0, h3019, h3025, hlam]
            · linarith only [h2760, h2761, h3023, h3024, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3045 | h3045
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3046 | h3046
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3047 | h3047
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3048 | h3048
                  · linarith only [h2760, h2761, h3047, h3048, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3050 | h3050
                    · linarith only [h2760, h2761, h3023, h3048, h3050, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3052 | h3052
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3053 | h3053
                        · linarith only [h2760, h2761, h3023, h3046, h3048, h3053, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3055 | h3055
                          · linarith only [h2760, h2761, h3023, h3046, h3047, h3055, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3057 | h3057
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3058 | h3058
                              · rcases h3bigk with h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3023, h3046, hc23, hc35, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2760, h2761, h3048, hc23, hc34, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3021, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3023, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2760, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h2760, h2761, h3048, hc23, hc34, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3048, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3050, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3019, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3046, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3053, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3055, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  rcases p3059_3 (m.d 0 3) (by simp) with h3075 | h3075
                                  · linarith only [h3075, hlam, p3059_0]
                                  · rcases p3059_3 (m.d 1 3) (by simp) with h3077 | h3077
                                    · linarith only [h3048, h3077, hlam]
                                    · rcases p3059_3 (m.d 2 3) (by simp) with h3079 | h3079
                                      · linarith only [h3053, h3079, hlam]
                                      · rcases p3059_3 (m.d 3 4) (by simp) with h3081 | h3081
                                        · rcases p3059_3 (m.d 3 5) (by simp) with h3082 | h3082
                                          · linarith only [h3058, h3082, hlam]
                                          · linarith only [h3023, h3082, hlam]
                                        · linarith only [h3081, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  rcases p3059_3 (m.d 0 3) (by simp) with h3086 | h3086
                                  · linarith only [h3021, h3086, hlam]
                                  · linarith only [h2760, h3086, hlam]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  rcases p3059_3 (m.d 0 3) (by simp) with h3089 | h3089
                                  · linarith only [h3021, h3089, hlam]
                                  · linarith only [h3019, h3089, hlam]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3023, hc03, hc34, hlam, hphi, p3059_1]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  rcases p3059_3 (m.d 0 3) (by simp) with h3094 | h3094
                                  · linarith only [h3094, hlam, p3059_0]
                                  · rcases p3059_3 (m.d 1 3) (by simp) with h3096 | h3096
                                    · linarith only [h3050, h3096, hlam]
                                    · rcases p3059_3 (m.d 2 3) (by simp) with h3098 | h3098
                                      · linarith only [h3055, h3098, hlam]
                                      · rcases p3059_3 (m.d 3 4) (by simp) with h3100 | h3100
                                        · rcases p3059_3 (m.d 3 5) (by simp) with h3101 | h3101
                                          · rcases h4bigk with h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h2761, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3057, hc04, hlam, hphi, ht0b, ht45, ht5b, p3102_1, u4ehi4]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3021, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              rcases p3102_3 (m.d 0 4) (by simp) with h3107 | h3107
                                              · rcases p3102_3 (m.d 1 4) (by simp) with h3108 | h3108
                                                · rcases p3102_3 (m.d 2 4) (by simp) with h3109 | h3109
                                                  · linarith only [h3020, h3109, hlam]
                                                  · linarith only [h3057, h3109, hlam]
                                                · linarith only [h3052, h3108, hlam]
                                              · linarith only [h3107, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h2760, h2761, h3046, h3048, hc23, hc34, hlam, hphi, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3048, h3057, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3102_1, u4ehi4]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3048, hlam, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              rcases p3102_3 (m.d 0 4) (by simp) with h3118 | h3118
                                              · linarith only [h2761, h3118, hlam]
                                              · linarith only [h3045, h3118, hlam]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3020, hlam, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3047, hlam, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3053, hlam, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3020, hc02, hlam, hphi, ht0b, ht45, ht5b, p3102_1, u4ehi4]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h2760, h2761, h3046, hc23, hc34, hlam, hphi, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h2760, h2761, h3046, hc23, hc34, hlam, hphi, p3102_1]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3057, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3102_1, u4ehi4]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              rcases p3102_3 (m.d 0 4) (by simp) with h3130 | h3130
                                              · linarith only [h3021, h3130, hlam]
                                              · linarith only [h3045, h3130, hlam]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3045, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3052, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3057, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [h3058, hlam, p3102_0]
                                            · have p3102_0 := h3102c.1
                                              have p3102_1 := h3102c.2.1
                                              have p3102_2 := h3102c.2.2.1
                                              have p3102_3 := h3102c.2.2.2
                                              linarith only [hlam, p3102_0]
                                          · linarith only [h3101, hlam, p3059_0]
                                        · linarith only [h3021, h3100, hlam]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  rcases p3059_3 (m.d 0 3) (by simp) with h3140 | h3140
                                  · linarith only [h3023, h3140, hlam]
                                  · linarith only [h2760, h3140, hlam]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  rcases p3059_3 (m.d 0 3) (by simp) with h3143 | h3143
                                  · linarith only [h3023, h3143, hlam]
                                  · linarith only [h3019, h3143, hlam]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [h3058, hlam, p3059_0]
                                · have p3059_0 := h3059c.1
                                  have p3059_1 := h3059c.2.1
                                  have p3059_2 := h3059c.2.2.1
                                  have p3059_3 := h3059c.2.2.2
                                  linarith only [hlam, p3059_0]
                              · linarith only [h0, h3020, h3057, h3058, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3149 | h3149
                              · rcases h3bigk with h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c | h3150c
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h2760, h2761, h3046, h3048, hc23, hc34, hlam, hphi, p3150_1]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h2760, h2761, h3048, hc23, hc34, hlam, hphi, p3150_1]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3021, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3023, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h2760, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h2760, h2761, h3048, hc23, hc34, hlam, hphi, p3150_1]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3048, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3050, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3019, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3046, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3053, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3055, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  rcases p3150_3 (m.d 0 3) (by simp) with h3166 | h3166
                                  · linarith only [h3166, hlam, p3150_0]
                                  · rcases p3150_3 (m.d 1 3) (by simp) with h3168 | h3168
                                    · linarith only [h3048, h3168, hlam]
                                    · rcases p3150_3 (m.d 2 3) (by simp) with h3170 | h3170
                                      · linarith only [h3053, h3170, hlam]
                                      · rcases p3150_3 (m.d 3 4) (by simp) with h3172 | h3172
                                        · rcases p3150_3 (m.d 3 5) (by simp) with h3173 | h3173
                                          · linarith only [h3149, h3173, hlam]
                                          · linarith only [h3023, h3173, hlam]
                                        · linarith only [h3172, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  rcases p3150_3 (m.d 0 3) (by simp) with h3177 | h3177
                                  · linarith only [h3021, h3177, hlam]
                                  · linarith only [h2760, h3177, hlam]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  rcases p3150_3 (m.d 0 3) (by simp) with h3180 | h3180
                                  · linarith only [h3021, h3180, hlam]
                                  · linarith only [h3019, h3180, hlam]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3023, hc03, hc34, hlam, hphi, p3150_1]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  rcases p3150_3 (m.d 0 3) (by simp) with h3185 | h3185
                                  · linarith only [h3185, hlam, p3150_0]
                                  · rcases p3150_3 (m.d 1 3) (by simp) with h3187 | h3187
                                    · linarith only [h3050, h3187, hlam]
                                    · rcases p3150_3 (m.d 2 3) (by simp) with h3189 | h3189
                                      · linarith only [h3055, h3189, hlam]
                                      · rcases p3150_3 (m.d 3 4) (by simp) with h3191 | h3191
                                        · rcases p3150_3 (m.d 3 5) (by simp) with h3192 | h3192
                                          · rcases h4bigk with h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h2761, hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              rcases p3193_3 (m.d 0 4) (by simp) with h3196 | h3196
                                              · rcases p3193_3 (m.d 1 4) (by simp) with h3197 | h3197
                                                · rcases p3193_3 (m.d 2 4) (by simp) with h3198 | h3198
                                                  · linarith only [h3020, h3198, hlam]
                                                  · rcases p3193_3 (m.d 3 4) (by simp) with h3200 | h3200
                                                    · rcases p3193_3 (m.d 4 5) (by simp) with h3201 | h3201
                                                      · linarith only [h3045, h3201, hlam]
                                                      · linarith only [h3057, h3201, hlam]
                                                    · linarith only [h3053, h3200, hlam]
                                                · linarith only [h3047, h3197, hlam]
                                              · linarith only [h3020, h3196, hlam]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3021, hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h0, h3020, h3057, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3193_1, u4ehi2]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h2760, h2761, h3046, h3048, hc23, hc34, hlam, hphi, p3193_1]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              rcases p3193_3 (m.d 0 4) (by simp) with h3211 | h3211
                                              · linarith only [h2761, h3211, hlam]
                                              · linarith only [h3020, h3211, hlam]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3048, hlam, p3193_1]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3048, h3057, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3193_1, u4ehi2]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3020, hlam, p3193_1]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3047, hlam, p3193_1]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3053, hlam, p3193_1]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3057, hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3045, h3057, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3193_1, u4ehi2]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h2760, h2761, h3046, hc23, hc34, hlam, hphi, p3193_1]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              rcases p3193_3 (m.d 0 4) (by simp) with h3223 | h3223
                                              · linarith only [h3021, h3223, hlam]
                                              · linarith only [h3020, h3223, hlam]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3057, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3193_1, u4ehi2]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3045, hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3052, hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3045, hc04, hlam, hphi, ht0b, ht45, ht5b, p3193_1, u4ehi2]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [h3149, hlam, p3193_0]
                                            · have p3193_0 := h3193c.1
                                              have p3193_1 := h3193c.2.1
                                              have p3193_2 := h3193c.2.2.1
                                              have p3193_3 := h3193c.2.2.2
                                              linarith only [hlam, p3193_0]
                                          · linarith only [h3192, hlam, p3150_0]
                                        · linarith only [h3021, h3191, hlam]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  rcases p3150_3 (m.d 0 3) (by simp) with h3235 | h3235
                                  · linarith only [h3023, h3235, hlam]
                                  · linarith only [h2760, h3235, hlam]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  rcases p3150_3 (m.d 0 3) (by simp) with h3238 | h3238
                                  · linarith only [h3023, h3238, hlam]
                                  · linarith only [h3019, h3238, hlam]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [h3149, hlam, p3150_0]
                                · have p3150_0 := h3150c.1
                                  have p3150_1 := h3150c.2.1
                                  have p3150_2 := h3150c.2.2.1
                                  have p3150_3 := h3150c.2.2.2
                                  linarith only [hlam, p3150_0]
                              · linarith only [h2761, h3045, h3048, h3149, hlam]
                      · linarith only [h2761, h3045, h3052, hlam]
                · linarith only [h0, h3020, h3047, hlam]
              · linarith only [h0, h3019, h3046, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3247 | h3247
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3248 | h3248
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3249 | h3249
                  · linarith only [h2760, h2761, h3248, h3249, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3251 | h3251
                    · linarith only [h2760, h3023, h3251, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3253 | h3253
                      · linarith only [h2760, h2761, h3045, h3249, h3253, hc13, hc34, hlam, hphi]
                      · linarith only [h2760, h2761, h3247, h3253, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h3020, h3248, hlam]
              · linarith only [h0, h3019, h3247, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3258 | h3258
        · linarith only [h0, h2760, h3020, h3258, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3260 | h3260
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3261 | h3261
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3262 | h3262
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3263 | h3263
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3264 | h3264
                  · linarith only [h0, h2760, h3020, h3258, h3263, h3264, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3266 | h3266
                    · linarith only [h0, h2760, h3020, h3263, h3266, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h2760, h3020, h3260, h3263, h3266, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3269 | h3269
                  · linarith only [h0, h2760, h3263, h3269, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3271 | h3271
                    · linarith only [h0, h2760, h3263, h3271, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h2760, h3260, h3263, h3271, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h2760, h3019, h3260, h3262, hc02, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h2760, h3020, h3260, h3261, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3276 | h3276
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3277 | h3277
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3278 | h3278
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3279 | h3279
                  · linarith only [h0, h2760, h3279, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3281 | h3281
                    · linarith only [h0, h2760, h3020, h3278, h3281, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3283 | h3283
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3284 | h3284
                        · linarith only [h0, h2760, h3020, h3277, h3278, h3279, h3284, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3286 | h3286
                          · linarith only [h0, h2760, h3020, h3260, h3277, h3278, h3286, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3288 | h3288
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3289 | h3289
                              · rcases h3bigk with h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3260, h3277, hc23, hc35, hlam, hphi, p3290_1]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h0, h2760, h3020, h3278, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3290_1]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3258, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3260, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h2760, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h0, h2760, h3020, h3278, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3290_1]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3279, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3281, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3019, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3277, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3284, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3286, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  rcases p3290_3 (m.d 0 3) (by simp) with h3306 | h3306
                                  · linarith only [h3306, hlam, p3290_0]
                                  · rcases p3290_3 (m.d 1 3) (by simp) with h3308 | h3308
                                    · linarith only [h3279, h3308, hlam]
                                    · rcases p3290_3 (m.d 2 3) (by simp) with h3310 | h3310
                                      · linarith only [h3284, h3310, hlam]
                                      · rcases p3290_3 (m.d 3 4) (by simp) with h3312 | h3312
                                        · rcases p3290_3 (m.d 3 5) (by simp) with h3313 | h3313
                                          · linarith only [h3289, h3313, hlam]
                                          · linarith only [h3260, h3313, hlam]
                                        · linarith only [h3312, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  rcases p3290_3 (m.d 0 3) (by simp) with h3317 | h3317
                                  · linarith only [h3258, h3317, hlam]
                                  · linarith only [h2760, h3317, hlam]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  rcases p3290_3 (m.d 0 3) (by simp) with h3320 | h3320
                                  · linarith only [h3258, h3320, hlam]
                                  · linarith only [h3019, h3320, hlam]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3260, hc03, hc34, hlam, hphi, p3290_1]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  rcases p3290_3 (m.d 0 3) (by simp) with h3325 | h3325
                                  · linarith only [h3325, hlam, p3290_0]
                                  · rcases p3290_3 (m.d 1 3) (by simp) with h3327 | h3327
                                    · linarith only [h3281, h3327, hlam]
                                    · rcases p3290_3 (m.d 2 3) (by simp) with h3329 | h3329
                                      · linarith only [h3286, h3329, hlam]
                                      · rcases p3290_3 (m.d 3 4) (by simp) with h3331 | h3331
                                        · rcases p3290_3 (m.d 3 5) (by simp) with h3332 | h3332
                                          · rcases h4bigk with h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h2761, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3020, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3258, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3020, h3278, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3333_1, u4ehi4]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3276, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3333_1, u4ehi4]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h0, h3020, h3278, hc01, hc12, hlam, hphi, p3333_1]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3279, hlam, p3333_1]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              rcases p3333_3 (m.d 0 4) (by simp) with h3343 | h3343
                                              · linarith only [h2761, h3343, hlam]
                                              · linarith only [h3276, h3343, hlam]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3276, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3333_1, u4ehi4]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3278, hlam, p3333_1]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3284, hlam, p3333_1]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3278, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3333_1, u4ehi4]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3276, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3333_1, u4ehi4]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h2760, h2761, h3277, hc23, hc34, hlam, hphi, p3333_1]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h0, h2760, h3020, h3277, hc23, hc34, hlam, hphi, p3333_1]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              rcases p3333_3 (m.d 0 4) (by simp) with h3355 | h3355
                                              · linarith only [h3258, h3355, hlam]
                                              · linarith only [h3276, h3355, hlam]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3276, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3283, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3288, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [h3289, hlam, p3333_0]
                                            · have p3333_0 := h3333c.1
                                              have p3333_1 := h3333c.2.1
                                              have p3333_2 := h3333c.2.2.1
                                              have p3333_3 := h3333c.2.2.2
                                              linarith only [hlam, p3333_0]
                                          · linarith only [h3332, hlam, p3290_0]
                                        · linarith only [h3258, h3331, hlam]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  rcases p3290_3 (m.d 0 3) (by simp) with h3365 | h3365
                                  · linarith only [h3260, h3365, hlam]
                                  · linarith only [h2760, h3365, hlam]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  rcases p3290_3 (m.d 0 3) (by simp) with h3368 | h3368
                                  · linarith only [h3260, h3368, hlam]
                                  · linarith only [h3019, h3368, hlam]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [h3289, hlam, p3290_0]
                                · have p3290_0 := h3290c.1
                                  have p3290_1 := h3290c.2.1
                                  have p3290_2 := h3290c.2.2.1
                                  have p3290_3 := h3290c.2.2.2
                                  linarith only [hlam, p3290_0]
                              · linarith only [h3020, h3276, h3278, h3289, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h3020, h3276, h3288, hlam]
                      · linarith only [h3020, h3276, h3278, h3283, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3376 | h3376
                  · linarith only [h0, h2760, h3258, h3278, h3376, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3378 | h3378
                    · linarith only [h0, h2760, h3278, h3378, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3380 | h3380
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3381 | h3381
                        · linarith only [h0, h2760, h3277, h3278, h3376, h3381, hlam]
                        · linarith only [h0, h2760, h3277, h3278, h3381, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2760, h3276, h3277, h3278, h3380, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h2760, h3019, h3277, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3386 | h3386
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3387 | h3387
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3388 | h3388
                  · linarith only [h0, h2760, h3388, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3390 | h3390
                    · linarith only [h0, h2760, h3020, h3387, h3390, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3392 | h3392
                      · linarith only [h2760, h2761, h3276, h3386, h3388, h3392, hc23, hc34, hlam, hphi]
                      · linarith only [h2760, h2761, h3386, h3392, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3395 | h3395
                  · linarith only [h0, h2760, h3395, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3397 | h3397
                    · linarith only [h0, h2760, h3387, h3397, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3399 | h3399
                      · linarith only [h0, h2760, h3020, h3276, h3386, h3395, h3399, hc23, hc34, hlam, hphi]
                      · linarith only [h2760, h2761, h3386, h3399, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h2760, h3019, h3386, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h2760, h3019, hlam]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3405 | h3405
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3406 | h3406
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3407 | h3407
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3408 | h3408
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3409 | h3409
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3410 | h3410
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3411 | h3411
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3412 | h3412
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3413 | h3413
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3414 | h3414
                    · linarith only [h2760, h3404, h3414, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2760, h3404, h3409, h3410, h3412, h3414, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h2760, h3404, h3405, h3408, h3413, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h2760, h3404, h3409, h3412, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h0, h3404, h3409, h3411, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h3404, h3409, h3410, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3421 | h3421
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3422 | h3422
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3423 | h3423
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3424 | h3424
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3425 | h3425
                    · linarith only [h2760, h3404, h3409, h3421, h3425, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3427 | h3427
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3428 | h3428
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3429 | h3429
                          · linarith only [h3404, h3409, h3422, h3429, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3431 | h3431
                            · linarith only [h3404, h3409, h3422, h3427, h3431, hlam]
                            · rcases h3bigk with h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c | h3433c
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h2760, hlam, p3433_1]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3428, h3431, hc03, hlam, hphi, ht0b, ht45, ht5b, p3433_1, u4ehi3]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                rcases p3433_3 (m.d 0 3) (by simp) with h3437 | h3437
                                · rcases p3433_3 (m.d 1 3) (by simp) with h3438 | h3438
                                  · rcases p3433_3 (m.d 2 3) (by simp) with h3439 | h3439
                                    · linarith only [h3405, h3439, hlam]
                                    · linarith only [h3427, h3439, hlam]
                                  · linarith only [h3423, h3438, hlam]
                                · linarith only [h3437, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                rcases p3433_3 (m.d 0 3) (by simp) with h3444 | h3444
                                · rcases p3433_3 (m.d 1 3) (by simp) with h3445 | h3445
                                  · rcases p3433_3 (m.d 2 3) (by simp) with h3446 | h3446
                                    · linarith only [h3405, h3446, hlam]
                                    · linarith only [h3428, h3446, hlam]
                                  · linarith only [h3424, h3445, hlam]
                                · linarith only [h3444, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h2760, h3404, h3421, h3422, h3427, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3433_1, u4ehi3]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3421, h3428, h3431, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3433_1, u4ehi3]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                rcases p3433_3 (m.d 0 3) (by simp) with h3454 | h3454
                                · linarith only [h2760, h3454, hlam]
                                · linarith only [h3407, h3454, hlam]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                rcases p3433_3 (m.d 0 3) (by simp) with h3457 | h3457
                                · linarith only [h2760, h3457, hlam]
                                · linarith only [h3408, h3457, hlam]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3405, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3421, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3405, hc02, hlam, hphi, ht0b, ht45, ht5b, p3433_1, u4ehi3]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h0, h3405, h3431, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3433_1, u4ehi3]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3407, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3423, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3427, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3431, hlam, p3433_1]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3408, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3424, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3428, hlam, p3433_0]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [h3408, hc03, hlam, hphi, ht0b, ht45, ht5b, p3433_1, u4ehi3]
                              · have p3433_0 := h3433c.1
                                have p3433_1 := h3433c.2.1
                                have p3433_2 := h3433c.2.2.1
                                have p3433_3 := h3433c.2.2.2
                                linarith only [hlam, p3433_0]
                        · linarith only [h3408, h3427, h3428, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3476 | h3476
                        · linarith only [h2760, h3404, h3421, h3423, h3427, h3476, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3478 | h3478
                          · linarith only [h2760, h3404, h3409, h3421, h3423, h3427, h3478, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3480 | h3480
                            · linarith only [h3404, h3409, h3423, h3480, hlam]
                            · rcases h3bigk with h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c | h3482c
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h2760, hlam, p3482_1]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                rcases p3482_3 (m.d 0 3) (by simp) with h3485 | h3485
                                · rcases p3482_3 (m.d 1 3) (by simp) with h3486 | h3486
                                  · rcases p3482_3 (m.d 2 3) (by simp) with h3487 | h3487
                                    · linarith only [h3405, h3487, hlam]
                                    · rcases p3482_3 (m.d 3 4) (by simp) with h3489 | h3489
                                      · linarith only [h3407, h3489, hlam]
                                      · linarith only [h3427, h3489, hlam]
                                  · linarith only [h3421, h3486, hlam]
                                · linarith only [h3405, h3485, hlam]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                rcases p3482_3 (m.d 0 3) (by simp) with h3494 | h3494
                                · rcases p3482_3 (m.d 1 3) (by simp) with h3495 | h3495
                                  · rcases p3482_3 (m.d 2 3) (by simp) with h3496 | h3496
                                    · linarith only [h3405, h3496, hlam]
                                    · rcases p3482_3 (m.d 3 4) (by simp) with h3498 | h3498
                                      · linarith only [h3498, hlam, p3482_0]
                                      · rcases p3482_3 (m.d 3 5) (by simp) with h3500 | h3500
                                        · linarith only [h3408, h3500, hlam]
                                        · linarith only [h3480, h3500, hlam]
                                  · linarith only [h3423, h3495, hlam]
                                · linarith only [h3494, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                rcases p3482_3 (m.d 0 3) (by simp) with h3505 | h3505
                                · rcases p3482_3 (m.d 1 3) (by simp) with h3506 | h3506
                                  · rcases p3482_3 (m.d 2 3) (by simp) with h3507 | h3507
                                    · linarith only [h3405, h3507, hlam]
                                    · rcases p3482_3 (m.d 3 4) (by simp) with h3509 | h3509
                                      · linarith only [h3407, h3509, hlam]
                                      · rcases p3482_3 (m.d 3 5) (by simp) with h3511 | h3511
                                        · linarith only [h3511, hlam, p3482_0]
                                        · rcases h4bigk with h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c | h3513c
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3409, hc45, hlam, hphi, p3513_1, u4ehi1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3409, hc45, hlam, hphi, p3513_1, u4ehi2]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3409, h3427, hc23, hc45, hlam, hphi, ht34, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3409, hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3404, hlam, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h2760, h3404, h3421, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3513_1, u4ehi2]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h2760, h3404, h3421, h3427, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3425, hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3406, hlam, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3422, hlam, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3427, hlam, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3478, hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3407, hlam, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3423, hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h2760, h3407, h3421, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3513_1, u4ehi2]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3480, hlam, p3513_0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hc45, hlam, hphi, p3513_1, u4ehi0]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hc45, hlam, hphi, p3513_1, u4ehi1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hc45, hlam, hphi, p3513_1, u4ehi2]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [h3427, hc23, hc45, hlam, hphi, ht34, p3513_1]
                                          · have p3513_0 := h3513c.1
                                            have p3513_1 := h3513c.2.1
                                            have p3513_2 := h3513c.2.2.1
                                            have p3513_3 := h3513c.2.2.2
                                            linarith only [hlam, p3513_0]
                                  · linarith only [h3424, h3506, hlam]
                                · linarith only [h3505, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h2760, h3404, h3421, h3423, h3427, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3482_1]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h2760, h3404, h3423, h3427, hlam, p3482_2]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                rcases p3482_3 (m.d 0 3) (by simp) with h3544 | h3544
                                · linarith only [h2760, h3544, hlam]
                                · linarith only [h3407, h3544, hlam]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                rcases p3482_3 (m.d 0 3) (by simp) with h3547 | h3547
                                · linarith only [h2760, h3547, hlam]
                                · linarith only [h3408, h3547, hlam]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3405, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3421, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3427, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3476, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3407, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3423, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h2760, h3404, h3423, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3482_1]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3480, hlam, p3482_1]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3408, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3424, hlam, p3482_0]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                rcases p3482_3 (m.d 0 3) (by simp) with h3562 | h3562
                                · rcases p3482_3 (m.d 1 3) (by simp) with h3563 | h3563
                                  · rcases p3482_3 (m.d 2 3) (by simp) with h3564 | h3564
                                    · linarith only [h3564, hlam, p3482_0]
                                    · rcases p3482_3 (m.d 3 4) (by simp) with h3566 | h3566
                                      · linarith only [h3480, h3566, hlam]
                                      · linarith only [h3427, h3566, hlam]
                                  · linarith only [h3421, h3563, hlam]
                                · linarith only [h3405, h3562, hlam]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [h3408, hc03, hlam, hphi, ht0b, ht45, ht5b, p3482_1, u4ehi3]
                              · have p3482_0 := h3482c.1
                                have p3482_1 := h3482c.2.1
                                have p3482_2 := h3482c.2.2.1
                                have p3482_3 := h3482c.2.2.2
                                linarith only [hlam, p3482_0]
                  · linarith only [h2760, h3408, h3424, hlam]
                · linarith only [h2760, h3404, h3423, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h2760, h3404, h3421, h3422, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h3404, h3421, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3577 | h3577
          · linarith only [h2760, h3404, h3408, h3577, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3579 | h3579
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3580 | h3580
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3581 | h3581
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3582 | h3582
                  · linarith only [h2760, h3404, h3408, h3579, h3580, h3582, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h2760, h3404, h3580, h3582, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h2760, h3404, h3580, h3581, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h0, h3404, h3580, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h3404, h3405, h3408, h3579, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
      · linarith only [h2760, h3404, h3407, hlam]
    · linarith only [h0, h3404, h3406, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3590 | h3590
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3591 | h3591
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3592 | h3592
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3593 | h3593
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3594 | h3594
            · linarith only [h0, h3404, h3405, h3593, h3594, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h0, h3404, h3593, h3594, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3597 | h3597
            · linarith only [h3405, h3590, h3597, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h0, h3404, h3597, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3600 | h3600
          · linarith only [h0, h3404, h3405, h3592, h3600, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3602 | h3602
            · linarith only [h0, h3404, h3405, h3602, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h0, h3404, h3602, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h3404, h3405, h3591, hlam]
    · linarith only [h0, h3404, h3590, hlam]

end R2N4
