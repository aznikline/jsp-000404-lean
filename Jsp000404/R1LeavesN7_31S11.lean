import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2838 | h2838
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2839 | h2839
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2840 | h2840
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2841 | h2841
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2842 | h2842
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2843 | h2843
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2844 | h2844
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2845 | h2845
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2846 | h2846
                  · linarith only [h0, h2837, h2846, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h2837, h2841, h2846, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h2839, h2845, hlam]
              · linarith only [h0, h2838, h2840, h2844, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2837, h2843, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2852 | h2852
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2853 | h2853
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2854 | h2854
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2855 | h2855
                  · linarith only [h0, h2837, h2855, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h2837, h2841, h2852, h2855, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h2839, h2854, hlam]
              · linarith only [h0, h2838, h2840, h2853, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2837, h2852, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2861 | h2861
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2862 | h2862
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2863 | h2863
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2864 | h2864
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2865 | h2865
                  · linarith only [h0, h2837, h2841, h2865, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2867 | h2867
                    · linarith only [h0, h2837, h2867, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2869 | h2869
                      · linarith only [h0, h2838, h2869, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h2838, h2861, h2865, h2869, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h2839, h2864, hlam]
              · linarith only [h0, h2839, h2840, h2863, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h2837, h2862, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2875 | h2875
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2876 | h2876
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2877 | h2877
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2878 | h2878
                  · linarith only [h0, h2837, h2878, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2880 | h2880
                    · linarith only [h0, h2838, h2878, h2880, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2882 | h2882
                      · linarith only [h0, h2838, h2882, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2884 | h2884
                        · linarith only [h2837, h2841, h2875, h2884, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2886 | h2886
                          · linarith only [h0, h2839, h2861, h2876, h2882, h2886, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2888 | h2888
                            · rcases h1bigk with h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c | h2889c
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h0, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2889_1, u1elo1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2889_1, u1elo1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p2889_1, u1elo1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [hc01, hlam, hphi, p2889_1, u1elo1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                rcases p2889_3 (m.d 0 1) (by simp) with h2897 | h2897
                                · linarith only [h0, h2897, hlam]
                                · linarith only [h2837, h2897, hlam]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                rcases p2889_3 (m.d 0 1) (by simp) with h2900 | h2900
                                · linarith only [h0, h2900, hlam]
                                · linarith only [h2838, h2900, hlam]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                rcases p2889_3 (m.d 0 1) (by simp) with h2903 | h2903
                                · linarith only [h0, h2903, hlam]
                                · linarith only [h2839, h2903, hlam]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2837, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2875, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2878, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2880, hlam, p2889_1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2838, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2876, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2839, h2875, h2882, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2889_1, u1elo0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2882, hlam, p2889_1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2839, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h2877, hlam, p2889_0]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h0, h2839, h2875, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2889_1, u1elo1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [h0, h2839, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2889_1, u1elo1]
                              · have p2889_0 := h2889c.1
                                have p2889_1 := h2889c.2.1
                                have p2889_2 := h2889c.2.2.1
                                have p2889_3 := h2889c.2.2.2
                                linarith only [hlam, p2889_0]
                            · rcases h1bigk with h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, h2875, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2921_1, u1elo1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, h2876, h2884, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2921_1, u1elo1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p2921_1, u1elo1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hc01, hlam, hphi, p2921_1, u1elo1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 1) (by simp) with h2929 | h2929
                                · linarith only [h0, h2929, hlam]
                                · linarith only [h2837, h2929, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 1) (by simp) with h2932 | h2932
                                · linarith only [h0, h2932, hlam]
                                · linarith only [h2838, h2932, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 1) (by simp) with h2935 | h2935
                                · linarith only [h0, h2935, hlam]
                                · linarith only [h2839, h2935, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2837, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2875, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2878, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2880, hlam, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2838, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2876, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2838, h2875, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2921_1, u1elo0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2882, hlam, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2839, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2877, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, h2839, h2875, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2921_1, u1elo1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, h2839, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2921_1, u1elo1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                · linarith only [h0, h2839, h2877, hlam]
              · linarith only [h0, h2839, h2840, h2876, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h2837, h2875, hlam]
      · linarith only [h0, h2838, h2840, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2957 | h2957
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2958 | h2958
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2959 | h2959
          · linarith only [h2837, h2839, h2958, h2959, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2961 | h2961
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2962 | h2962
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2963 | h2963
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2964 | h2964
                  · linarith only [h2837, h2839, h2963, h2964, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h2837, h2839, h2958, h2963, h2964, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2967 | h2967
                  · linarith only [h0, h2837, h2963, h2967, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2837, h2958, h2963, h2967, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h2837, h2957, h2958, h2962, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2837, h2961, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2972 | h2972
          · linarith only [h2838, h2839, h2972, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2974 | h2974
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2975 | h2975
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2976 | h2976
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2977 | h2977
                  · linarith only [h2837, h2839, h2958, h2976, h2977, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2979 | h2979
                    · linarith only [h2838, h2839, h2976, h2977, h2979, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2981 | h2981
                      · linarith only [h2838, h2839, h2972, h2976, h2981, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2983 | h2983
                        · linarith only [h2837, h2958, h2974, h2983, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2985 | h2985
                          · linarith only [h2838, h2839, h2975, h2981, h2985, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2987 | h2987
                            · linarith only [h2838, h2839, h2977, h2981, h2987, hc13, hc34, hlam, hphi]
                            · rcases h1bigk with h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h0, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2839, h2974, h2976, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2989_1, u1elo1]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2839, h2976, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2989_1, u1elo1]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2839, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hc01, hlam, hphi, p2989_1, u1elo1]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                rcases p2989_3 (m.d 0 1) (by simp) with h2997 | h2997
                                · linarith only [h0, h2997, hlam]
                                · linarith only [h2837, h2997, hlam]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                rcases p2989_3 (m.d 0 1) (by simp) with h3000 | h3000
                                · linarith only [h0, h3000, hlam]
                                · linarith only [h2838, h3000, hlam]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2838, h2839, h2974, h2977, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2989_1, u1elo1]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2837, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2974, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2977, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2979, hlam, p2989_1]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2838, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2975, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2838, h2974, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2989_1, u1elo0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2981, hlam, p2989_1]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hc01, hlam, hphi, p2989_1, u1elo4]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [h2976, hlam, p2989_0]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                rcases p2989_3 (m.d 0 1) (by simp) with h3016 | h3016
                                · linarith only [h2839, h3016, hlam]
                                · linarith only [h2837, h3016, hlam]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                rcases p2989_3 (m.d 0 1) (by simp) with h3019 | h3019
                                · linarith only [h2839, h3019, hlam]
                                · linarith only [h2838, h3019, hlam]
                              · have p2989_0 := h2989c.1
                                have p2989_1 := h2989c.2.1
                                have p2989_2 := h2989c.2.2.1
                                have p2989_3 := h2989c.2.2.2
                                linarith only [hlam, p2989_0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3023 | h3023
                  · linarith only [h2837, h2958, h3023, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3025 | h3025
                    · linarith only [h0, h2837, h2976, h3025, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3027 | h3027
                      · linarith only [h0, h2838, h2976, h3027, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3029 | h3029
                        · linarith only [h0, h2838, h2958, h2974, h2976, h3023, h3029, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3031 | h3031
                          · linarith only [h0, h2838, h2957, h2976, h3027, h3031, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h2838, h2974, h2976, h3023, h3031, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h2957, h2975, hlam]
            · linarith only [h0, h2837, h2974, hlam]
      · linarith only [h0, h2838, h2957, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3037 | h3037
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3038 | h3038
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3039 | h3039
        · linarith only [h2837, h2838, h3039, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3041 | h3041
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3042 | h3042
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3043 | h3043
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3044 | h3044
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3045 | h3045
                  · linarith only [h2837, h2838, h3039, h3043, h3045, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3047 | h3047
                    · linarith only [h2837, h2838, h3043, h3047, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3049 | h3049
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3050 | h3050
                        · linarith only [h2838, h3042, h3045, h3050, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3052 | h3052
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3053 | h3053
                            · rcases h1bigk with h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c | h3054c
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h0, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h2838, h3042, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3054_1, u1elo3]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h2838, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h2838, h3042, h3047, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3054_1, u1elo3]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [hc01, hlam, hphi, p3054_1, u1elo1]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                rcases p3054_3 (m.d 0 1) (by simp) with h3062 | h3062
                                · linarith only [h0, h3062, hlam]
                                · linarith only [h2837, h3062, hlam]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h2838, h3037, h3042, h3047, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3054_1, u1elo1]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                rcases p3054_3 (m.d 0 1) (by simp) with h3066 | h3066
                                · linarith only [h0, h3066, hlam]
                                · linarith only [h3037, h3066, hlam]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h2837, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3042, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3045, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3047, hlam, p3054_1]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3037, h3042, h3047, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3054_1, u1elo3]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3043, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                rcases p3054_3 (m.d 0 1) (by simp) with h3076 | h3076
                                · linarith only [h2838, h3076, hlam]
                                · linarith only [h2837, h3076, hlam]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                rcases p3054_3 (m.d 0 1) (by simp) with h3080 | h3080
                                · linarith only [h2838, h3080, hlam]
                                · linarith only [h3037, h3080, hlam]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3037, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3044, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3037, h3042, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3054_1, u1elo0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [h3049, hlam, p3054_0]
                              · have p3054_0 := h3054c.1
                                have p3054_1 := h3054c.2.1
                                have p3054_2 := h3054c.2.2.1
                                have p3054_3 := h3054c.2.2.2
                                linarith only [hlam, p3054_0]
                            · linarith only [h2838, h3038, h3045, h3052, h3053, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · linarith only [h2838, h3037, h3049, h3052, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · linarith only [h2838, h3037, h3047, h3049, hc13, hc45, hlam, hphi, ht34]
                · linarith only [h2838, h3037, h3043, h3044, hlam]
              · linarith only [h0, h3038, h3043, hlam]
            · linarith only [h0, h2837, h2838, h3038, h3042, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h2838, h3037, h3041, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3095 | h3095
        · linarith only [h0, h2837, h3038, h3095, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3097 | h3097
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3098 | h3098
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3099 | h3099
              · linarith only [h0, h3038, h3099, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3101 | h3101
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3102 | h3102
                  · linarith only [h2837, h3095, h3102, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3104 | h3104
                    · linarith only [h0, h2837, h3099, h3104, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3106 | h3106
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3107 | h3107
                        · linarith only [h3098, h3099, h3102, h3107, hlam]
                        · linarith only [h0, h3037, h3099, h3104, h3107, hc13, hc34, hlam, hphi]
                      · linarith only [h0, h3037, h3098, h3099, h3104, h3106, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h3037, h3101, hlam]
            · linarith only [h0, h2837, h3098, hlam]
          · linarith only [h0, h3037, h3038, h3097, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3114 | h3114
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3115 | h3115
        · linarith only [h2837, h2838, h3115, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3117 | h3117
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3118 | h3118
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3119 | h3119
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3120 | h3120
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3121 | h3121
                  · linarith only [h2837, h3037, h3115, h3121, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3123 | h3123
                    · linarith only [h2837, h2838, h3119, h3123, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3125 | h3125
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3126 | h3126
                        · linarith only [h3037, h3118, h3121, h3125, h3126, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3128 | h3128
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3129 | h3129
                            · rcases h1bigk with h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h0, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3037, h3118, h3125, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3130_1, u1elo3]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2838, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3037, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [hc01, hlam, hphi, p3130_1, u1elo1]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                rcases p3130_3 (m.d 0 1) (by simp) with h3138 | h3138
                                · linarith only [h0, h3138, hlam]
                                · linarith only [h2837, h3138, hlam]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2837, h2838, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3130_1, u1elo1]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2837, h3037, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3130_1, u1elo1]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2837, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3118, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3121, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3123, hlam, p3130_1]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2837, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3130_1, u1elo3]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3119, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                rcases p3130_3 (m.d 0 1) (by simp) with h3150 | h3150
                                · linarith only [h2838, h3150, hlam]
                                · linarith only [h2837, h3150, hlam]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2837, h3037, h3118, h3119, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3130_1, u1elo1]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h2837, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3130_1, u1elo4]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3120, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                rcases p3130_3 (m.d 0 1) (by simp) with h3157 | h3157
                                · linarith only [h3037, h3157, hlam]
                                · linarith only [h2837, h3157, hlam]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [h3125, hlam, p3130_0]
                              · have p3130_0 := h3130c.1
                                have p3130_1 := h3130c.2.1
                                have p3130_2 := h3130c.2.2.1
                                have p3130_3 := h3130c.2.2.2
                                linarith only [hlam, p3130_0]
                            · linarith only [h0, h3114, h3121, h3128, h3129, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3163 | h3163
                            · rcases h1bigk with h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h0, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3037, h3118, h3125, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3164_1, u1elo3]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2838, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3037, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [hc01, hlam, hphi, p3164_1, u1elo1]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                rcases p3164_3 (m.d 0 1) (by simp) with h3172 | h3172
                                · linarith only [h0, h3172, hlam]
                                · linarith only [h2837, h3172, hlam]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2837, h2838, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3164_1, u1elo1]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2837, h3037, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3164_1, u1elo1]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2837, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3118, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3121, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3123, hlam, p3164_1]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2837, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3164_1, u1elo3]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3119, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                rcases p3164_3 (m.d 0 1) (by simp) with h3184 | h3184
                                · linarith only [h2838, h3184, hlam]
                                · linarith only [h2837, h3184, hlam]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2837, h3037, h3118, h3119, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3164_1, u1elo1]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h2837, h3118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3164_1, u1elo4]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3120, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                rcases p3164_3 (m.d 0 1) (by simp) with h3191 | h3191
                                · linarith only [h3037, h3191, hlam]
                                · linarith only [h2837, h3191, hlam]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [h3125, hlam, p3164_0]
                              · have p3164_0 := h3164c.1
                                have p3164_1 := h3164c.2.1
                                have p3164_2 := h3164c.2.2.1
                                have p3164_3 := h3164c.2.2.2
                                linarith only [hlam, p3164_0]
                            · linarith only [h2837, h2838, h3117, h3118, h3121, h3163, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h2838, h3117, h3125, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3198 | h3198
                  · linarith only [h2837, h2838, h3198, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3200 | h3200
                    · linarith only [h2837, h2838, h3200, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3202 | h3202
                      · linarith only [h3119, h3120, h3202, hlam]
                      · linarith only [h0, h2837, h2838, h3114, h3117, h3118, h3120, h3202, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h3114, h3119, hlam]
            · linarith only [h0, h2837, h3118, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3207 | h3207
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3208 | h3208
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3209 | h3209
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3210 | h3210
                  · linarith only [h2837, h2838, h3115, h3210, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3212 | h3212
                    · linarith only [h2837, h2838, h3208, h3212, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3214 | h3214
                      · linarith only [h2838, h3117, h3208, h3214, hc01, hlam, hphi, u1elo1]
                      · linarith only [h2837, h2838, h3207, h3214, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3217 | h3217
                  · linarith only [h2837, h2838, h3217, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3219 | h3219
                    · linarith only [h2837, h2838, h3219, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3221 | h3221
                      · linarith only [h2838, h3117, h3208, h3209, h3221, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h2837, h2838, h3207, h3221, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h2837, h3114, h3207, h3208, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h2837, h3207, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3226 | h3226
        · linarith only [h0, h2837, h3114, h3226, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3228 | h3228
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3229 | h3229
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3230 | h3230
              · linarith only [h0, h3114, h3230, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3232 | h3232
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3233 | h3233
                  · linarith only [h2837, h3226, h3233, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3235 | h3235
                    · linarith only [h2837, h3037, h3230, h3232, h3235, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3237 | h3237
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3238 | h3238
                        · linarith only [h3229, h3230, h3233, h3238, hlam]
                        · linarith only [h2837, h3037, h3230, h3232, h3238, hc13, hc34, hlam, hphi]
                      · linarith only [h2837, h3037, h3228, h3229, h3230, h3232, h3237, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3242 | h3242
                  · linarith only [h0, h2837, h3232, h3242, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3244 | h3244
                    · linarith only [h0, h2837, h3232, h3244, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3246 | h3246
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3247 | h3247
                        · linarith only [h0, h2837, h3229, h3232, h3242, h3246, h3247, hlam]
                        · linarith only [h0, h2837, h3229, h3230, h3247, hc23, hc34, hlam, hphi]
                      · linarith only [h2838, h3228, h3246, hlam]
            · linarith only [h0, h2837, h3229, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3252 | h3252
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3253 | h3253
              · linarith only [h0, h2837, h3114, h3252, h3253, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3255 | h3255
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3256 | h3256
                  · linarith only [h0, h2837, h3253, h3256, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3258 | h3258
                    · linarith only [h2837, h3037, h3253, h3255, h3258, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3260 | h3260
                      · linarith only [h2838, h3228, h3260, hc01, hlam, hphi, u1elo3]
                      · linarith only [h2837, h2838, h3252, h3260, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3263 | h3263
                  · linarith only [h0, h2837, h3253, h3263, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3265 | h3265
                    · linarith only [h0, h2837, h3253, h3265, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3267 | h3267
                      · linarith only [h0, h3114, h3228, h3267, hc01, hlam, hphi, u1elo3]
                      · linarith only [h2837, h2838, h3252, h3267, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h2837, h3252, hlam]

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3271 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3272 | h3272
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3273 | h3273
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3274 | h3274
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3275 | h3275
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3276 | h3276
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3277 | h3277
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3278 | h3278
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3279 | h3279
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3280 | h3280
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3281 | h3281
                    · linarith only [h2837, h3271, h3276, h3281, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h2837, h3271, h3275, h3276, h3281, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h2837, h3272, h3280, hlam]
                · linarith only [h2837, h3272, h3274, h3279, hc03, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h2837, h3272, h3276, h3278, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h2837, h3272, h3273, h3276, h3277, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3288 | h3288
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3289 | h3289
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3290 | h3290
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3291 | h3291
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3292 | h3292
                    · linarith only [h0, h3271, h3276, h3292, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h3271, h3275, h3276, h3290, h3292, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h3272, h3276, h3291, hlam]
                · linarith only [h2837, h3274, h3290, hlam]
              · linarith only [h0, h3272, h3289, hlam]
            · linarith only [h0, h3273, h3288, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3299 | h3299
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3300 | h3300
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3301 | h3301
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3302 | h3302
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3303 | h3303
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3304 | h3304
                    · linarith only [h2837, h3271, h3275, h3299, h3304, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3306 | h3306
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3307 | h3307
                        · linarith only [h3271, h3275, h3300, h3307, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3309 | h3309
                          · linarith only [h3271, h3275, h3300, h3306, h3309, hlam]
                          · rcases h1bigk with h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h0, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h2837, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h2837, h3299, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3311_1, u1elo1]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h2837, h3299, hc15, hlam, hphi, ht01, ht0b, ht5b, p3311_1, u1elo1]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [hc01, hlam, hphi, p3311_1, u1elo1]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h2837, hc01, hlam, hphi, p3311_1, u1elo1]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              rcases p3311_3 (m.d 0 1) (by simp) with h3320 | h3320
                              · linarith only [h0, h3320, hlam]
                              · linarith only [h3271, h3320, hlam]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              rcases p3311_3 (m.d 0 1) (by simp) with h3323 | h3323
                              · linarith only [h0, h3323, hlam]
                              · linarith only [h3272, h3323, hlam]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3272, h3300, h3304, h3306, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3311_1, u1elo2]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3299, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              rcases p3311_3 (m.d 0 1) (by simp) with h3329 | h3329
                              · linarith only [h2837, h3329, hlam]
                              · linarith only [h3271, h3329, hlam]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              rcases p3311_3 (m.d 0 1) (by simp) with h3332 | h3332
                              · linarith only [h2837, h3332, hlam]
                              · linarith only [h3272, h3332, hlam]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3271, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3300, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3302, hlam, p3311_1]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3304, hlam, p3311_1]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3272, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3301, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3303, hlam, p3311_0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [h3272, h3300, h3306, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3311_1, u1elo0]
                            · have p3311_0 := h3311c.1
                              have p3311_1 := h3311c.2.1
                              have p3311_2 := h3311c.2.2.1
                              have p3311_3 := h3311c.2.2.2
                              linarith only [hlam, p3311_0]
                      · linarith only [h2837, h3271, h3299, h3302, h3306, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h2837, h3272, h3303, hlam]
                · linarith only [h2837, h3274, h3302, hlam]
              · linarith only [h2837, h3272, h3299, h3301, hlam]
            · linarith only [h0, h3273, h3300, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3350 | h3350
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3351 | h3351
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3352 | h3352
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3353 | h3353
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3354 | h3354
                    · linarith only [h3271, h3275, h3354, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3356 | h3356
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3357 | h3357
                        · linarith only [h3271, h3275, h3350, h3357, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3359 | h3359
                          · linarith only [h3271, h3275, h3350, h3356, h3359, hlam]
                          · rcases h1bigk with h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h0, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h2837, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h0, h3299, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3361_1, u1elo2]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h0, h3299, h3350, h3354, h3356, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3361_1, u1elo2]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3299, hc01, hlam, hphi, p3361_1, u1elo2]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3299, hlam, p3361_1]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              rcases p3361_3 (m.d 0 1) (by simp) with h3370 | h3370
                              · linarith only [h0, h3370, hlam]
                              · linarith only [h3271, h3370, hlam]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              rcases p3361_3 (m.d 0 1) (by simp) with h3373 | h3373
                              · linarith only [h0, h3373, hlam]
                              · linarith only [h3272, h3373, hlam]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3272, h3350, h3354, h3356, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3361_1, u1elo2]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h0, h3272, h3350, h3354, h3356, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3361_1, u1elo2]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              rcases p3361_3 (m.d 0 1) (by simp) with h3379 | h3379
                              · linarith only [h2837, h3379, hlam]
                              · linarith only [h3271, h3379, hlam]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              rcases p3361_3 (m.d 0 1) (by simp) with h3382 | h3382
                              · linarith only [h2837, h3382, hlam]
                              · linarith only [h3272, h3382, hlam]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3271, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3350, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3352, hlam, p3361_1]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3354, hlam, p3361_1]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3272, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3351, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h3353, hlam, p3361_0]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [h0, h3272, h3350, h3356, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3361_1, u1elo1]
                            · have p3361_0 := h3361c.1
                              have p3361_1 := h3361c.2.1
                              have p3361_2 := h3361c.2.2.1
                              have p3361_3 := h3361c.2.2.2
                              linarith only [hlam, p3361_0]
                      · linarith only [h0, h3272, h3299, h3351, h3356, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h2837, h3272, h3353, hlam]
                · linarith only [h0, h3271, h3274, h3299, h3352, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h3272, h3351, hlam]
            · linarith only [h0, h3273, h3350, hlam]
      · linarith only [h2837, h3271, h3274, hlam]
    · linarith only [h0, h3271, h3273, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3402 | h3402
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3403 | h3403
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3404 | h3404
        · linarith only [h3271, h3272, h3404, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3406 | h3406
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3407 | h3407
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3408 | h3408
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3409 | h3409
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3410 | h3410
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3411 | h3411
                    · linarith only [h3271, h3272, h3404, h3406, h3410, h3411, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3413 | h3413
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3414 | h3414
                        · linarith only [h3271, h3272, h3407, h3411, h3414, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3416 | h3416
                          · linarith only [h3271, h3272, h3407, h3411, h3413, h3416, hlam]
                          · rcases h1bigk with h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c | h3418c
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h0, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h2837, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3272, h3406, h3410, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3418_1, u1elo1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3272, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [hc01, hlam, hphi, p3418_1, u1elo1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3410, hc35, hlam, hphi, ht01, ht0b, ht5b, p3418_1, u1elo1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              rcases p3418_3 (m.d 0 1) (by simp) with h3427 | h3427
                              · linarith only [h0, h3427, hlam]
                              · linarith only [h3271, h3427, hlam]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3271, h3272, h3407, h3413, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3418_1, u1elo1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3271, h3407, h3413, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3418_1, u1elo2]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3406, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              rcases p3418_3 (m.d 0 1) (by simp) with h3434 | h3434
                              · linarith only [h2837, h3434, hlam]
                              · linarith only [h3271, h3434, hlam]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3271, h3272, h3406, h3407, h3413, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3418_1, u1elo1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3271, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3407, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3409, hlam, p3418_1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3411, hlam, p3418_1]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3271, h3407, h3413, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3418_1, u1elo4]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3408, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [h3410, hlam, p3418_0]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              rcases p3418_3 (m.d 0 1) (by simp) with h3446 | h3446
                              · linarith only [h3272, h3446, hlam]
                              · linarith only [h3271, h3446, hlam]
                            · have p3418_0 := h3418c.1
                              have p3418_1 := h3418c.2.1
                              have p3418_2 := h3418c.2.2.1
                              have p3418_3 := h3418c.2.2.2
                              linarith only [hlam, p3418_0]
                      · linarith only [h3271, h3272, h3406, h3409, h3410, h3413, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3451 | h3451
                    · linarith only [h2837, h3271, h3451, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3453 | h3453
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3454 | h3454
                        · linarith only [h2837, h3271, h3407, h3410, h3451, h3454, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3456 | h3456
                          · linarith only [h2837, h3271, h3407, h3410, h3451, h3453, h3456, hlam]
                          · linarith only [h2837, h3271, h3407, h3410, h3453, h3456, hc34, hc45, hlam, hphi]
                      · linarith only [h2837, h3403, h3410, h3453, hc23, hc35, hlam, hphi]
                · linarith only [h2837, h3271, h3403, h3409, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3461 | h3461
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3462 | h3462
                  · linarith only [h3406, h3408, h3462, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3464 | h3464
                    · linarith only [h2837, h3271, h3462, h3464, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3466 | h3466
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3467 | h3467
                        · linarith only [h2837, h3271, h3406, h3407, h3408, h3464, h3467, hlam]
                        · linarith only [h2837, h3271, h3406, h3408, h3467, hc14, hc45, hlam, hphi]
                      · linarith only [h2837, h3403, h3462, h3466, hc23, hc35, hlam, hphi]
                · linarith only [h2837, h3271, h3403, h3461, hlam]
            · linarith only [h0, h3402, h3407, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3473 | h3473
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3474 | h3474
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3475 | h3475
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3476 | h3476
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3477 | h3477
                    · linarith only [h0, h3271, h3406, h3477, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3479 | h3479
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3480 | h3480
                        · linarith only [h3271, h3272, h3473, h3477, h3480, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3482 | h3482
                          · linarith only [h3271, h3272, h3473, h3477, h3479, h3482, hlam]
                          · rcases h1bigk with h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h0, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h2837, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3272, h3406, h3474, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3484_1, u1elo2]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3272, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3406, hc01, hlam, hphi, p3484_1, u1elo2]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3406, hlam, p3484_1]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              rcases p3484_3 (m.d 0 1) (by simp) with h3493 | h3493
                              · linarith only [h0, h3493, hlam]
                              · linarith only [h3271, h3493, hlam]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3271, h3272, h3406, h3473, h3479, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3484_1, u1elo2]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3271, h3473, h3479, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3484_1, u1elo2]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3474, hc25, hlam, hphi, ht01, ht0b, ht5b, p3484_1, u1elo2]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              rcases p3484_3 (m.d 0 1) (by simp) with h3500 | h3500
                              · linarith only [h2837, h3500, hlam]
                              · linarith only [h3271, h3500, hlam]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3271, h3272, h3473, h3479, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3484_1, u1elo2]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3271, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3473, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3475, hlam, p3484_1]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3477, hlam, p3484_1]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3271, h3473, h3474, h3479, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3484_1, u1elo1]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3474, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [h3476, hlam, p3484_0]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              rcases p3484_3 (m.d 0 1) (by simp) with h3512 | h3512
                              · linarith only [h3272, h3512, hlam]
                              · linarith only [h3271, h3512, hlam]
                            · have p3484_0 := h3484c.1
                              have p3484_1 := h3484c.2.1
                              have p3484_2 := h3484c.2.2.1
                              have p3484_3 := h3484c.2.2.2
                              linarith only [hlam, p3484_0]
                      · linarith only [h0, h3271, h3406, h3473, h3479, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h3406, h3474, h3476, hlam]
                · linarith only [h2837, h3403, h3475, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3519 | h3519
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3520 | h3520
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3521 | h3521
                    · linarith only [h0, h3271, h3474, h3520, h3521, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3523 | h3523
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3524 | h3524
                        · linarith only [h0, h3271, h3473, h3474, h3521, h3524, hlam]
                        · linarith only [h0, h3271, h3474, h3524, hc14, hc45, hlam, hphi]
                      · linarith only [h0, h3271, h3403, h3406, h3523, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3528 | h3528
                    · linarith only [h0, h3271, h3528, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3530 | h3530
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3531 | h3531
                        · linarith only [h0, h3271, h3406, h3473, h3520, h3528, h3531, hlam]
                        · linarith only [h0, h3271, h3474, h3531, hc14, hc45, hlam, hphi]
                      · linarith only [h0, h3271, h3406, h3473, h3530, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h3271, h3403, h3406, h3519, hlam]
            · linarith only [h0, h3271, h3402, h3473, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h2837, h3271, h3403, hlam]
    · linarith only [h0, h3271, h3402, hlam]

end R2N4
