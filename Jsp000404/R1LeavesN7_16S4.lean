import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5802000 in
set_option maxHeartbeats 5802000 in
theorem r1l7_21_15_H_I_L_I_s5 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_21_15_H_I_L_I_s6 m hb1 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2825 | h2825
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2826 | h2826
      · linarith only [h2826, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2828 | h2828
        · linarith only [h2828, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2830 | h2830
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2831 | h2831
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2832 | h2832
              · linarith only [h0, h2832, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2834 | h2834
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2835 | h2835
                  · linarith only [h1, h2826, h2835, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2837 | h2837
                    · linarith only [h2, h2828, h2837, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2839 | h2839
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2840 | h2840
                        · linarith only [h0, h2826, h2830, h2840, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2842 | h2842
                          · linarith only [h2, h2828, h2831, h2842, hlam]
                          · linarith only [h0, h2830, h2839, h2842, h6, hc34, hc45, hlam, hphi]
                      · linarith only [h2825, h2826, h2839, hc23, hc35, hlam, hphi]
                · linarith only [h2825, h2826, h2830, h2834, hc23, hc35, hlam, hphi]
            · linarith only [h2830, h2831, h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2830, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2849 | h2849
      · linarith only [h2849, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2851 | h2851
        · linarith only [h2851, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2853 | h2853
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2854 | h2854
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2855 | h2855
              · linarith only [h0, h2855, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2857 | h2857
                · linarith only [h1, h2825, h2857, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2859 | h2859
                  · linarith only [h0, h1, h2825, h2849, h2853, h2859, h6, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2861 | h2861
                    · linarith only [h2, h2851, h2861, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2863 | h2863
                      · linarith only [h0, h2825, h2853, h2863, h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2865 | h2865
                        · linarith only [h2849, h2865, h4, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2867 | h2867
                          · linarith only [h0, h1, h2825, h2851, h2854, h2867, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2869 | h2869
                            · linarith only [h2867, h2869, h4, h6, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2854, h2863, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                rcases p2871_3 (m.d 0 1) (by simp) with h2874 | h2874
                                · rcases p2871_3 (m.d 1 2) (by simp) with h2875 | h2875
                                  · linarith only [h0, h2875, hlam]
                                  · linarith only [h2853, h2875, hlam]
                                · linarith only [h2874, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                rcases p2871_3 (m.d 0 1) (by simp) with h2879 | h2879
                                · rcases p2871_3 (m.d 1 2) (by simp) with h2880 | h2880
                                  · linarith only [h0, h2880, hlam]
                                  · linarith only [h2854, h2880, hlam]
                                · linarith only [h2879, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2854, h2855, h2863, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h0, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h0, h2853, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h0, h2865, h2869, h6, hc14, hc45, hlam, hphi, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2855, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h1, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2853, hlam, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2857, hlam, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2859, hlam, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2854, hlam, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2, h2853, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2861, hlam, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h3, hlam, p2871_0]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2853, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [h2865, h2869, h3, h6, hc14, hc45, hlam, hphi, p2871_1]
                              · have p2871_0 := h2871c.1
                                have p2871_1 := h2871c.2.1
                                have p2871_2 := h2871c.2.2.1
                                have p2871_3 := h2871c.2.2.2
                                linarith only [hlam, p2871_0]
            · linarith only [h2854, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h2853, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 6176000 in
set_option maxHeartbeats 6176000 in
theorem r1l7_21_15_H_I_L_I_s4 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_21_15_H_I_L_I_s5 m hb1 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2907 | h2907
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2908 | h2908
      · linarith only [h2908, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2910 | h2910
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2911 | h2911
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2912 | h2912
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2913 | h2913
              · linarith only [h0, h2913, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2915 | h2915
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2916 | h2916
                  · linarith only [h1, h2908, h2916, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2918 | h2918
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2919 | h2919
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2920 | h2920
                        · linarith only [h0, h2908, h2912, h2920, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2922 | h2922
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2923 | h2923
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2924 | h2924
                              · rcases h1bigk with h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c | h2925c
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2912, h2922, h2924, hc01, hc45, hlam, hphi, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2912, h2922, h2924, hc01, hc45, hlam, hphi, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2912, h2913, h2922, h2924, hc01, hc45, hlam, hphi, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  rcases p2925_3 (m.d 0 1) (by simp) with h2930 | h2930
                                  · rcases p2925_3 (m.d 1 2) (by simp) with h2931 | h2931
                                    · linarith only [h0, h2931, hlam]
                                    · linarith only [h2915, h2931, hlam]
                                  · linarith only [h2930, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h0, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2912, h2922, h2924, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2913, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h0, h2920, h5, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h1, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2912, hlam, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2916, hlam, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h1, h2915, hc01, hc25, hlam, hphi, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h0, h2, h2912, h2920, h2922, h2924, h5, hc01, hc13, hc34, hc45, hlam, hphi, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2, h2918, h2924, hc01, hc45, hlam, hphi, ht0b, ht5b, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h3, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2915, hlam, p2925_1]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2918, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [h2919, hlam, p2925_0]
                                · have p2925_0 := h2925c.1
                                  have p2925_1 := h2925c.2.1
                                  have p2925_2 := h2925c.2.2.1
                                  have p2925_3 := h2925c.2.2.2
                                  linarith only [hlam, p2925_0]
                              · linarith only [h0, h2912, h2920, h2924, h5, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h2912, h2919, h2922, h2923, h5, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2910, h2920, h2922, h4, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h2908, h2910, h2911, h2912, h2913, h2919, hc23, hc34, hlam, hphi]
                    · linarith only [h2908, h2910, h2918, hc13, hc34, hlam, hphi]
                · linarith only [h2907, h2912, h2915, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h2912, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2910, h2911, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2963 | h2963
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2964 | h2964
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2965 | h2965
              · linarith only [h0, h2907, h2965, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2967 | h2967
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2968 | h2968
                  · linarith only [h1, h2908, h2968, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2970 | h2970
                    · linarith only [h1, h2910, h2970, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2972 | h2972
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2973 | h2973
                        · linarith only [h0, h1, h2908, h2964, h2973, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2975 | h2975
                          · linarith only [h2910, h2964, h2970, h2975, h3, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2977 | h2977
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2978 | h2978
                              · rcases h1bigk with h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c | h2979c
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2964, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  rcases p2979_3 (m.d 0 1) (by simp) with h2982 | h2982
                                  · rcases p2979_3 (m.d 1 2) (by simp) with h2983 | h2983
                                    · linarith only [h0, h2983, hlam]
                                    · linarith only [h2964, h2983, hlam]
                                  · linarith only [h2982, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2965, h2967, h2975, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  rcases p2979_3 (m.d 0 1) (by simp) with h2988 | h2988
                                  · rcases p2979_3 (m.d 1 2) (by simp) with h2989 | h2989
                                    · linarith only [h0, h2989, hlam]
                                    · linarith only [h2967, h2989, hlam]
                                  · linarith only [h2988, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h0, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2965, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h0, h2973, h5, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h1, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2964, hlam, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2968, hlam, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2970, hlam, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2, h2964, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2, h2967, h2975, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h3, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2967, hlam, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2964, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2979_1]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [h2972, hlam, p2979_0]
                                · have p2979_0 := h2979c.1
                                  have p2979_1 := h2979c.2.1
                                  have p2979_2 := h2979c.2.2.1
                                  have p2979_3 := h2979c.2.2.2
                                  linarith only [hlam, p2979_0]
                              · linarith only [h2973, h2978, h4, h5, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h2907, h2972, h2977, h3, h5, hlam]
                      · linarith only [h2908, h2963, h2964, h2965, h2972, hc23, hc34, hlam, hphi]
                · linarith only [h2907, h2964, h2967, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h2964, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2907, h2963, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3019 | h3019
      · linarith only [h3019, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3021 | h3021
        · linarith only [h2907, h3021, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3023 | h3023
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3024 | h3024
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3025 | h3025
              · linarith only [h0, h3025, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3027 | h3027
                · linarith only [h0, h2907, h3027, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3029 | h3029
                  · linarith only [h1, h3019, h3029, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3031 | h3031
                    · linarith only [h1, h3021, h3031, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3033 | h3033
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3034 | h3034
                        · linarith only [h0, h1, h3019, h3024, h3034, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3036 | h3036
                          · linarith only [h3, h3021, h3027, h3034, h3036, h4, h5, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3038 | h3038
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3039 | h3039
                              · rcases h1bigk with h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3024, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  rcases p3040_3 (m.d 0 1) (by simp) with h3043 | h3043
                                  · rcases p3040_3 (m.d 1 2) (by simp) with h3044 | h3044
                                    · linarith only [h0, h3044, hlam]
                                    · linarith only [h3024, h3044, hlam]
                                  · linarith only [h3043, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3024, h3027, h3033, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3024, h3027, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h0, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h0, h2907, h3024, h3038, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3025, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3027, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h1, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3024, hlam, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3029, hlam, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3031, hlam, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2, h3024, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2, h3024, h3027, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3024, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2907, h3, h3024, h3034, h3038, hc23, hc34, hlam, hphi, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3033, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                              · linarith only [h0, h2907, h3024, h3034, h3038, h3039, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h3024, h3038, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h3019, h3023, h3024, h3025, h3033, hc23, hc34, hlam, hphi]
            · linarith only [h3024, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3074 | h3074
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3075 | h3075
              · linarith only [h0, h3075, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3077 | h3077
                · linarith only [h0, h2907, h3077, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3079 | h3079
                  · linarith only [h1, h3019, h3079, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3081 | h3081
                    · linarith only [h1, h3021, h3081, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3083 | h3083
                      · linarith only [h0, h2, h3023, h3074, h3083, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3085 | h3085
                        · linarith only [h0, h1, h3019, h3074, h3085, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3087 | h3087
                          · linarith only [h3021, h3023, h3087, h4, h5, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3089 | h3089
                            · linarith only [h0, h3023, h3074, h3085, h3089, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h3074, h3089, h5, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h3074, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_21_15_H_I_L_I_s4 m hb1 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3093 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3094 | h3094
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3095 | h3095
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3096 | h3096
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3097 | h3097
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3098 | h3098
          · linarith only [h0, h3093, h3098, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3100 | h3100
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3101 | h3101
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3102 | h3102
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3103 | h3103
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3104 | h3104
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3105 | h3105
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3106 | h3106
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3107 | h3107
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3108 | h3108
                            · rcases h1bigk with h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3100, h3105, h3108, hc01, hc45, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3098, h3100, h3105, h3108, hc01, hc45, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3100, h3105, h3108, hc01, hc45, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                rcases p3109_3 (m.d 0 1) (by simp) with h3114 | h3114
                                · rcases p3109_3 (m.d 1 2) (by simp) with h3115 | h3115
                                  · linarith only [h0, h3115, hlam]
                                  · linarith only [h3101, h3115, hlam]
                                · linarith only [h3114, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h0, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3098, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h0, h3100, h3105, h3108, hc02, hc45, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h0, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h1, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h1, h3100, h3105, h3108, hc01, hc45, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h1, h3101, h3106, hc01, hc35, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h2, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3100, hlam, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3102, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h2, h3101, h3106, hc01, hc35, hlam, hphi, ht0b, ht5b, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3101, hlam, p3109_1]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3103, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [h3104, hlam, p3109_0]
                              · have p3109_0 := h3109c.1
                                have p3109_1 := h3109c.2.1
                                have p3109_2 := h3109c.2.2.1
                                have p3109_3 := h3109c.2.2.2
                                linarith only [hlam, p3109_0]
                            · linarith only [h0, h3100, h3107, h3108, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3140 | h3140
                            · linarith only [h3105, h3107, h3140, hlam]
                            · rcases h1bigk with h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3100, h3105, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3098, h3100, h3105, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3104, h3105, h3107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3104, h3105, h3107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h0, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3098, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3104, h3105, h3107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h0, h3104, h3105, h3107, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h1, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h1, h3104, h3105, h3107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h1, h3104, h3105, h3107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h2, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3100, hlam, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3102, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h2, h3093, h3104, h3105, h3107, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3101, hlam, p3142_1]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3103, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [h3104, hlam, p3142_0]
                              · have p3142_0 := h3142c.1
                                have p3142_1 := h3142c.2.1
                                have p3142_2 := h3142c.2.2.1
                                have p3142_3 := h3142c.2.2.2
                                linarith only [hlam, p3142_0]
                        · linarith only [h3096, h3106, h4, hlam]
                      · linarith only [h3095, h3105, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3170 | h3170
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3171 | h3171
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3172 | h3172
                          · linarith only [h3100, h3104, h3172, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3174 | h3174
                            · linarith only [h3100, h3104, h3170, h3174, hlam]
                            · rcases h1bigk with h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3100, h3170, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3098, h3100, h3170, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                rcases p3176_3 (m.d 0 1) (by simp) with h3180 | h3180
                                · rcases p3176_3 (m.d 1 2) (by simp) with h3181 | h3181
                                  · linarith only [h0, h3181, hlam]
                                  · linarith only [h3100, h3181, hlam]
                                · linarith only [h3180, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                rcases p3176_3 (m.d 0 1) (by simp) with h3185 | h3185
                                · rcases p3176_3 (m.d 1 2) (by simp) with h3186 | h3186
                                  · linarith only [h0, h3186, hlam]
                                  · linarith only [h3101, h3186, hlam]
                                · linarith only [h3185, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h0, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3098, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h0, h3100, h3170, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h0, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h1, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h1, h3100, h3170, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h1, h3101, h3170, h3172, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h2, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3100, hlam, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3102, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3104, hlam, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3101, hlam, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3103, hlam, p3176_0]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [h3, h3100, h3170, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3176_1]
                              · have p3176_0 := h3176c.1
                                have p3176_1 := h3176c.2.1
                                have p3176_2 := h3176c.2.2.1
                                have p3176_3 := h3176c.2.2.2
                                linarith only [hlam, p3176_0]
                        · linarith only [h3093, h3097, h3100, h3104, h3170, h3171, h4, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h3093, h3097, h3104, h3170, h4, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h3098, h3101, h3103, hlam]
                · linarith only [h3098, h3100, h3102, hlam]
              · linarith only [h3094, h3100, h3101, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3093, h3100, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3216 | h3216
          · linarith only [h0, h3093, h3216, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3218 | h3218
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3219 | h3219
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3220 | h3220
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3221 | h3221
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3222 | h3222
                    · linarith only [h2, h3097, h3222, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3224 | h3224
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3225 | h3225
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3226 | h3226
                          · linarith only [h2, h3097, h3218, h3226, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3228 | h3228
                            · linarith only [h2, h3097, h3218, h3224, h3228, hlam]
                            · rcases h1bigk with h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3219, h3224, h3226, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3216, h3219, h3224, h3226, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                rcases p3230_3 (m.d 0 1) (by simp) with h3234 | h3234
                                · rcases p3230_3 (m.d 1 2) (by simp) with h3235 | h3235
                                  · linarith only [h0, h3235, hlam]
                                  · linarith only [h3218, h3235, hlam]
                                · linarith only [h3234, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                rcases p3230_3 (m.d 0 1) (by simp) with h3239 | h3239
                                · rcases p3230_3 (m.d 1 2) (by simp) with h3240 | h3240
                                  · linarith only [h0, h3240, hlam]
                                  · linarith only [h3219, h3240, hlam]
                                · linarith only [h3239, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h0, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3216, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h0, h3218, h3224, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h0, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h1, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3219, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h1, h3218, h3224, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h1, h3219, h3225, hc01, hc35, hlam, hphi, ht0b, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h2, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3218, hlam, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3220, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3222, hlam, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3219, hlam, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3221, hlam, p3230_0]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [h3, h3218, h3224, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3230_1]
                              · have p3230_0 := h3230c.1
                                have p3230_1 := h3230c.2.1
                                have p3230_2 := h3230c.2.2.1
                                have p3230_3 := h3230c.2.2.2
                                linarith only [hlam, p3230_0]
                        · linarith only [h3096, h3225, h4, hlam]
                      · linarith only [h3095, h3224, h4, hlam]
                  · linarith only [h3216, h3219, h3221, hlam]
                · linarith only [h3095, h3097, h3216, h3218, h3220, hc24, hc45, hlam, hphi]
              · linarith only [h3094, h3218, h3219, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3093, h3218, h4, hc12, hc23, hlam, hphi]
      · linarith only [h3094, h3096, h4, hlam]
    · linarith only [h3093, h3095, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3272 | h3272
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3273 | h3273
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3274 | h3274
        · linarith only [h3093, h3094, h3274, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3276 | h3276
          · linarith only [h0, h3276, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3278 | h3278
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3279 | h3279
              · linarith only [h0, h3094, h3279, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3281 | h3281
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3282 | h3282
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3283 | h3283
                    · linarith only [h2, h3274, h3283, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3285 | h3285
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3286 | h3286
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3287 | h3287
                          · linarith only [h0, h3094, h3274, h3278, h3287, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3289 | h3289
                            · linarith only [h0, h3094, h3272, h3278, h3287, h3289, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h1bigk with h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3278, h3285, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3278, h3279, h3282, h3285, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                rcases p3291_3 (m.d 0 1) (by simp) with h3295 | h3295
                                · rcases p3291_3 (m.d 1 2) (by simp) with h3296 | h3296
                                  · linarith only [h0, h3296, hlam]
                                  · linarith only [h3278, h3296, hlam]
                                · linarith only [h3295, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3278, h3279, h3285, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h0, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3276, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h0, h3094, h3278, h3285, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3279, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h1, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h1, h3278, h3285, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h1, h3278, h3279, h3285, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h2, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3278, hlam, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3281, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3283, hlam, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3278, h3285, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3282, hlam, p3291_0]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [h3, h3278, h3285, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3291_1]
                              · have p3291_0 := h3291c.1
                                have p3291_1 := h3291c.2.1
                                have p3291_2 := h3291c.2.2.1
                                have p3291_3 := h3291c.2.2.2
                                linarith only [hlam, p3291_0]
                        · linarith only [h1, h3282, h3286, h4, hlam]
                      · linarith only [h3272, h3285, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3323 | h3323
                    · linarith only [h3273, h3274, h3276, h3278, h3282, h3323, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3325 | h3325
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3326 | h3326
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3327 | h3327
                          · linarith only [h3273, h3274, h3276, h3278, h3282, h3327, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3329 | h3329
                            · linarith only [h3094, h3273, h3276, h3278, h3282, h3325, h3327, h3329, hlam]
                            · rcases h1bigk with h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3278, h3325, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3276, h3278, h3325, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                rcases p3331_3 (m.d 0 1) (by simp) with h3335 | h3335
                                · rcases p3331_3 (m.d 1 2) (by simp) with h3336 | h3336
                                  · linarith only [h0, h3336, hlam]
                                  · linarith only [h3278, h3336, hlam]
                                · linarith only [h3335, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3278, h3279, h3325, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h0, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3276, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3273, h3276, h3278, h3282, h3325, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3279, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h1, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3273, h3282, h4, hc12, hc23, hlam, hphi, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3273, h3278, h3282, h3325, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3282, hlam, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h2, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3278, hlam, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3281, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3323, hlam, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3, hlam, p3331_0]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3278, h3325, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3273, h3282, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [h3273, h3278, h3282, h3325, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3331_1]
                              · have p3331_0 := h3331c.1
                                have p3331_1 := h3331c.2.1
                                have p3331_2 := h3331c.2.2.1
                                have p3331_3 := h3331c.2.2.2
                                linarith only [hlam, p3331_0]
                        · linarith only [h3273, h3326, h4, hlam]
                      · linarith only [h0, h3272, h3278, h3325, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3272, h3274, h3276, h3278, h3281, hc24, hc45, hlam, hphi]
            · linarith only [h3093, h3094, h3278, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3365 | h3365
        · linarith only [h3093, h3273, h3365, h4, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3367 | h3367
          · linarith only [h0, h3367, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3369 | h3369
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3370 | h3370
              · linarith only [h0, h3094, h3370, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3372 | h3372
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3373 | h3373
                  · linarith only [h0, h1, h3273, h3369, h3373, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3375 | h3375
                    · linarith only [h2, h3365, h3375, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3377 | h3377
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3378 | h3378
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3379 | h3379
                          · linarith only [h0, h3273, h3365, h3369, h3378, h3379, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3381 | h3381
                            · linarith only [h3093, h3273, h3377, h3378, h3379, h3381, h4, hlam]
                            · rcases h1bigk with h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3369, h3377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3367, h3369, h3377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                rcases p3383_3 (m.d 0 1) (by simp) with h3387 | h3387
                                · rcases p3383_3 (m.d 1 2) (by simp) with h3388 | h3388
                                  · linarith only [h0, h3388, hlam]
                                  · linarith only [h3369, h3388, hlam]
                                · linarith only [h3387, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3367, h3369, h3373, h3377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h0, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3367, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h0, h3273, h3378, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3370, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h1, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3369, h3373, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h1, h3273, h3369, h3377, h3378, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3373, hlam, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h2, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3369, hlam, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3372, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3375, hlam, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3, hlam, p3383_0]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3, h3369, h3377, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3, h3273, h3378, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [h3, h3273, h3369, h3377, h3378, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3383_1]
                              · have p3383_0 := h3383c.1
                                have p3383_1 := h3383c.2.1
                                have p3383_2 := h3383c.2.2.1
                                have p3383_3 := h3383c.2.2.2
                                linarith only [hlam, p3383_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3413 | h3413
                          · linarith only [h0, h3369, h3378, h3413, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3415 | h3415
                            · linarith only [h0, h3369, h3377, h3378, h3413, h3415, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h3369, h3377, h3378, h3415, h4, hc34, hc45, hlam, hphi]
                      · linarith only [h3272, h3377, h4, hlam]
                · linarith only [h3272, h3273, h3372, hc13, hc35, hlam, hphi]
            · linarith only [h3093, h3273, h3369, h4, hc12, hc35, hlam, hphi, ht23]
    · linarith only [h3093, h3272, h4, hlam]

end R2N4
