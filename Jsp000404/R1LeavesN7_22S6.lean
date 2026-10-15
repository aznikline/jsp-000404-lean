import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S2
import Jsp000404.R1LeavesN7_22S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h2828 | h2828
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2829 | h2829
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2830 | h2830
      · linarith only [h0, h1557, h2830, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2832 | h2832
        · linarith only [h1, h1385, h1558, h2830, h2832, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2834 | h2834
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2835 | h2835
            · linarith only [h1, h1558, h2835, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2837 | h2837
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2838 | h2838
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2839 | h2839
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2840 | h2840
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2841 | h2841
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2842 | h2842
                        · rcases h0bigk with h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            rcases p2843_3 (m.d 0 1) (by simp) with h2845 | h2845
                            · rcases p2843_3 (m.d 0 2) (by simp) with h2846 | h2846
                              · linarith only [h0, h2846, hlam]
                              · rcases p2843_3 (m.d 0 3) (by simp) with h2848 | h2848
                                · linarith only [h1, h2848, hlam]
                                · linarith only [h2848, h4, hlam]
                            · linarith only [h0, h2845, hlam]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            rcases p2843_3 (m.d 0 1) (by simp) with h2852 | h2852
                            · rcases p2843_3 (m.d 0 2) (by simp) with h2853 | h2853
                              · linarith only [h0, h2853, hlam]
                              · rcases p2843_3 (m.d 0 3) (by simp) with h2855 | h2855
                                · linarith only [h1, h2855, hlam]
                                · rcases p2843_3 (m.d 0 4) (by simp) with h2857 | h2857
                                  · linarith only [h2, h2857, hlam]
                                  · linarith only [h1558, h2857, hlam]
                            · linarith only [h1, h2852, hlam]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            rcases p2843_3 (m.d 0 1) (by simp) with h2861 | h2861
                            · rcases p2843_3 (m.d 0 2) (by simp) with h2862 | h2862
                              · linarith only [h0, h2862, hlam]
                              · rcases p2843_3 (m.d 0 3) (by simp) with h2864 | h2864
                                · linarith only [h1, h2864, hlam]
                                · rcases p2843_3 (m.d 0 4) (by simp) with h2866 | h2866
                                  · linarith only [h2, h2866, hlam]
                                  · rcases p2843_3 (m.d 0 5) (by simp) with h2868 | h2868
                                    · linarith only [h2868, h3, hlam]
                                    · rcases h0emin with h2870 | h2870 | h2870 | h2870 | h2870
                                      · rcases h2bigk with h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h2834, h2840, h2842, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2871_1]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h4, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h1385, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h1558, h2840, h2842, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2843_1, p2871_1]
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
                                          linarith only [h2830, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h2832, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h0, h1558, h2840, h2842, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2843_1, p2871_1]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          rcases p2871_3 (m.d 0 2) (by simp) with h2882 | h2882
                                          · linarith only [h2882, hlam, p2871_0]
                                          · rcases p2871_3 (m.d 1 2) (by simp) with h2884 | h2884
                                            · linarith only [h2830, h2884, hlam]
                                            · rcases p2871_3 (m.d 2 3) (by simp) with h2886 | h2886
                                              · rcases p2871_3 (m.d 2 4) (by simp) with h2887 | h2887
                                                · linarith only [h2839, h2887, hlam]
                                                · linarith only [h1385, h2887, hlam]
                                              · linarith only [h2886, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          rcases p2871_3 (m.d 0 2) (by simp) with h2891 | h2891
                                          · linarith only [h2891, h4, hlam]
                                          · linarith only [h0, h2891, hlam]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h1558, h2839, h4, hc02, hc23, hlam, hphi, p2871_1]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h0, h1558, h2834, h2839, h4, hlam, p2871_2]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          rcases p2871_3 (m.d 0 2) (by simp) with h2897 | h2897
                                          · linarith only [h2897, hlam, p2871_0]
                                          · rcases p2871_3 (m.d 1 2) (by simp) with h2899 | h2899
                                            · linarith only [h2832, h2899, hlam]
                                            · rcases p2871_3 (m.d 2 3) (by simp) with h2901 | h2901
                                              · rcases p2871_3 (m.d 2 4) (by simp) with h2902 | h2902
                                                · rcases p2871_3 (m.d 2 5) (by simp) with h2903 | h2903
                                                  · linarith only [h2841, h2903, hlam]
                                                  · rcases h3bigk with h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h1558, h2830, h2834, h2839, h2840, h2842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h4, hlam, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h1558, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h1558, h2839, h2842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h1, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2830, hlam, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2835, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h1, h1558, h2839, h2842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      rcases p2905_3 (m.d 0 3) (by simp) with h2916 | h2916
                                                      · linarith only [h2916, h4, hlam]
                                                      · rcases p2905_3 (m.d 1 3) (by simp) with h2918 | h2918
                                                        · linarith only [h2830, h2918, hlam]
                                                        · rcases p2905_3 (m.d 2 3) (by simp) with h2920 | h2920
                                                          · rcases p2905_3 (m.d 3 4) (by simp) with h2921 | h2921
                                                            · linarith only [h2839, h2921, hlam]
                                                            · linarith only [h1558, h2921, hlam]
                                                          · linarith only [h2920, h4, hlam]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      rcases p2905_3 (m.d 0 3) (by simp) with h2925 | h2925
                                                      · linarith only [h2925, h4, hlam]
                                                      · linarith only [h1, h2925, hlam]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h0, h1558, h2834, h2840, h2842, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h0, h1558, h2834, h2839, h2840, h4, hlam, p2905_2]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h0, h2834, h2839, h2840, h2842, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2830, h2834, h2839, h2840, h2842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2839, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      rcases p2905_3 (m.d 0 3) (by simp) with h2935 | h2935
                                                      · linarith only [h1558, h2935, hlam]
                                                      · linarith only [h2828, h2935, hlam]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2828, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2837, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2840, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [h2842, hlam, p2905_0]
                                                    · have p2905_0 := h2905c.1
                                                      have p2905_1 := h2905c.2.1
                                                      have p2905_2 := h2905c.2.2.1
                                                      have p2905_3 := h2905c.2.2.2
                                                      linarith only [hlam, p2905_0]
                                                · linarith only [h2902, hlam, p2871_0]
                                              · linarith only [h2901, h4, hlam]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          rcases p2871_3 (m.d 0 2) (by simp) with h2945 | h2945
                                          · linarith only [h1385, h2945, hlam]
                                          · linarith only [h0, h2945, hlam]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h2839, hlam, p2871_1]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          rcases p2871_3 (m.d 0 2) (by simp) with h2950 | h2950
                                          · linarith only [h1385, h2950, hlam]
                                          · linarith only [h1557, h2950, hlam]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h1557, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h2834, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h2840, hlam, p2871_1]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [h2841, hlam, p2871_0]
                                        · have p2871_0 := h2871c.1
                                          have p2871_1 := h2871c.2.1
                                          have p2871_2 := h2871c.2.2.1
                                          have p2871_3 := h2871c.2.2.2
                                          linarith only [hlam, p2871_0]
                                      · linarith only [h2870, h4, hc23, hlam, ht01, ht12]
                                      · linarith only [h1558, h2839, h2870, hc23, hlam, ht01, ht12]
                                      · linarith only [h2870, hc01, hlam, p2843_1]
                                      · linarith only [h2870, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                            · linarith only [h2, h2861, hlam]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            rcases p2843_3 (m.d 0 1) (by simp) with h2963 | h2963
                            · rcases p2843_3 (m.d 0 2) (by simp) with h2964 | h2964
                              · linarith only [h0, h2964, hlam]
                              · linarith only [h1557, h2964, hlam]
                            · linarith only [h2963, h3, hlam]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h0, hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h4, hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1385, hlam, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1558, h2839, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1, hlam, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1558, h2839, hc02, hc23, hlam, hphi, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1558, hlam, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1558, h2839, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h2, hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1557, h1558, h2839, h2840, h2842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1557, h1558, h2839, h2840, h2842, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            rcases p2843_3 (m.d 0 1) (by simp) with h2982 | h2982
                            · rcases p2843_3 (m.d 0 2) (by simp) with h2983 | h2983
                              · linarith only [h1385, h2983, hlam]
                              · linarith only [h1557, h2983, hlam]
                            · linarith only [h2982, h3, hlam]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h3, hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h1557, hlam, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h2828, hlam, p2843_0]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [h2829, hlam, p2843_1]
                          · have p2843_0 := h2843c.1
                            have p2843_1 := h2843c.2.1
                            have p2843_2 := h2843c.2.2.1
                            have p2843_3 := h2843c.2.2.2
                            linarith only [hlam, p2843_0]
                        · linarith only [h1558, h2, h2842, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1558, h2838, h2839, h2841, h3, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                    · linarith only [h0, h1558, h2834, h2839, h2840, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2995 | h2995
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2996 | h2996
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2997 | h2997
                        · rcases h0bigk with h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3000 | h3000
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3001 | h3001
                              · linarith only [h0, h3001, hlam]
                              · rcases p2998_3 (m.d 0 3) (by simp) with h3003 | h3003
                                · linarith only [h1, h3003, hlam]
                                · linarith only [h3003, h4, hlam]
                            · linarith only [h0, h3000, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3007 | h3007
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3008 | h3008
                              · linarith only [h0, h3008, hlam]
                              · rcases p2998_3 (m.d 0 3) (by simp) with h3010 | h3010
                                · linarith only [h1, h3010, hlam]
                                · rcases p2998_3 (m.d 0 4) (by simp) with h3012 | h3012
                                  · linarith only [h2, h3012, hlam]
                                  · linarith only [h1558, h3012, hlam]
                            · linarith only [h1, h3007, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3016 | h3016
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3017 | h3017
                              · linarith only [h0, h3017, hlam]
                              · rcases p2998_3 (m.d 0 3) (by simp) with h3019 | h3019
                                · linarith only [h1, h3019, hlam]
                                · rcases p2998_3 (m.d 0 4) (by simp) with h3021 | h3021
                                  · linarith only [h2, h3021, hlam]
                                  · rcases p2998_3 (m.d 0 5) (by simp) with h3023 | h3023
                                    · linarith only [h3, h3023, hlam]
                                    · rcases h0emin with h3025 | h3025 | h3025 | h3025 | h3025
                                      · rcases h2bigk with h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2834, h2995, h2997, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h4, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h1385, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h0, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2830, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2832, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h0, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2839, hc02, hc34, hlam, hphi, ht23, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2839, hc12, hc34, hlam, hphi, ht23, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2839, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          rcases p3026_3 (m.d 0 2) (by simp) with h3041 | h3041
                                          · linarith only [h3041, h4, hlam]
                                          · linarith only [h1557, h3041, hlam]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          rcases p3026_3 (m.d 0 2) (by simp) with h3044 | h3044
                                          · linarith only [h3044, hlam, p3026_0]
                                          · rcases p3026_3 (m.d 1 2) (by simp) with h3046 | h3046
                                            · linarith only [h2832, h3046, hlam]
                                            · rcases p3026_3 (m.d 2 3) (by simp) with h3048 | h3048
                                              · linarith only [h2839, h3048, hlam]
                                              · linarith only [h3048, h4, hlam]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          rcases p3026_3 (m.d 0 2) (by simp) with h3051 | h3051
                                          · linarith only [h1385, h3051, hlam]
                                          · linarith only [h0, h3051, hlam]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h0, h2834, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          rcases p3026_3 (m.d 0 2) (by simp) with h3056 | h3056
                                          · linarith only [h1385, h3056, hlam]
                                          · linarith only [h1557, h3056, hlam]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h1557, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2834, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2995, hlam, p3026_1]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [h2996, hlam, p3026_0]
                                        · have p3026_0 := h3026c.1
                                          have p3026_1 := h3026c.2.1
                                          have p3026_2 := h3026c.2.2.1
                                          have p3026_3 := h3026c.2.2.2
                                          linarith only [hlam, p3026_0]
                                      · linarith only [h3025, h4, hc23, hlam, ht01, ht12]
                                      · linarith only [h1558, h3025, hc01, hlam, p2998_1]
                                      · linarith only [h3025, hc01, hlam, p2998_1]
                                      · linarith only [h3025, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                            · linarith only [h2, h3016, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3069 | h3069
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3070 | h3070
                              · linarith only [h0, h3070, hlam]
                              · linarith only [h1557, h3070, hlam]
                            · linarith only [h3, h3069, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h0, hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h4, hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h1385, hlam, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h2839, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h1, hlam, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h2839, h4, hc02, hc34, hlam, hphi, ht23, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h1558, hlam, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3083 | h3083
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3084 | h3084
                              · linarith only [h3084, h4, hlam]
                              · linarith only [h1557, h3084, hlam]
                            · linarith only [h3, h3083, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h2, hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3089 | h3089
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3090 | h3090
                              · linarith only [h1385, h3090, hlam]
                              · rcases p2998_3 (m.d 0 3) (by simp) with h3092 | h3092
                                · linarith only [h1558, h3092, hlam]
                                · linarith only [h3092, h4, hlam]
                            · linarith only [h0, h3089, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3096 | h3096
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3097 | h3097
                              · linarith only [h1385, h3097, hlam]
                              · rcases p2998_3 (m.d 0 3) (by simp) with h3099 | h3099
                                · linarith only [h1558, h3099, hlam]
                                · rcases p2998_3 (m.d 0 4) (by simp) with h3101 | h3101
                                  · rcases p2998_3 (m.d 0 5) (by simp) with h3102 | h3102
                                    · linarith only [h2829, h3102, hlam]
                                    · rcases h0emin with h3104 | h3104 | h3104 | h3104 | h3104
                                      · rcases h2bigk with h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c | h3105c
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2834, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h4, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h1385, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2995, h2997, h4, hc04, hc45, hlam, hphi, ht0b, ht5b, p2998_1, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h0, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2830, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2832, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h0, h1385, h2995, h2997, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2998_1, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2839, hc02, hc34, hlam, hphi, ht23, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2839, hc12, hc34, hlam, hphi, ht23, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2839, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          rcases p3105_3 (m.d 0 2) (by simp) with h3120 | h3120
                                          · linarith only [h3120, h4, hlam]
                                          · linarith only [h1557, h3120, hlam]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          rcases p3105_3 (m.d 0 2) (by simp) with h3123 | h3123
                                          · linarith only [h3123, hlam, p3105_0]
                                          · rcases p3105_3 (m.d 1 2) (by simp) with h3125 | h3125
                                            · linarith only [h2832, h3125, hlam]
                                            · rcases p3105_3 (m.d 2 3) (by simp) with h3127 | h3127
                                              · linarith only [h2839, h3127, hlam]
                                              · linarith only [h3127, h4, hlam]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          rcases p3105_3 (m.d 0 2) (by simp) with h3130 | h3130
                                          · linarith only [h1385, h3130, hlam]
                                          · linarith only [h0, h3130, hlam]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h0, h2834, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h1, h1385, h2830, h2834, hlam, p2998_1, p3105_2]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h1557, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2834, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2995, hlam, p3105_1]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [h2996, hlam, p3105_0]
                                        · have p3105_0 := h3105c.1
                                          have p3105_1 := h3105c.2.1
                                          have p3105_2 := h3105c.2.2.1
                                          have p3105_3 := h3105c.2.2.2
                                          linarith only [hlam, p3105_0]
                                      · linarith only [h3104, h4, hc23, hlam, ht01, ht12]
                                      · linarith only [h3104, hc04, hlam, p2998_1]
                                      · rcases h2bigk with h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h1385, h2834, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2998_1, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h4, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h1385, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h1385, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2998_1, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h0, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2830, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2832, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h0, h1385, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2998_1, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2839, hc02, hc34, hlam, hphi, ht23, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2839, hc12, hc34, hlam, hphi, ht23, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2839, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          rcases p3143_3 (m.d 0 2) (by simp) with h3158 | h3158
                                          · linarith only [h3158, h4, hlam]
                                          · linarith only [h1557, h3158, hlam]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          rcases p3143_3 (m.d 0 2) (by simp) with h3161 | h3161
                                          · linarith only [h3161, hlam, p3143_0]
                                          · rcases p3143_3 (m.d 1 2) (by simp) with h3163 | h3163
                                            · linarith only [h2832, h3163, hlam]
                                            · rcases p3143_3 (m.d 2 3) (by simp) with h3165 | h3165
                                              · linarith only [h2839, h3165, hlam]
                                              · linarith only [h3165, h4, hlam]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          rcases p3143_3 (m.d 0 2) (by simp) with h3168 | h3168
                                          · linarith only [h1385, h3168, hlam]
                                          · linarith only [h0, h3168, hlam]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h0, h2834, h2839, h2995, h2997, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h1, h1385, h2830, h2834, hlam, p2998_1, p3143_2]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h1557, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2834, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2995, hlam, p3143_1]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [h2996, hlam, p3143_0]
                                        · have p3143_0 := h3143c.1
                                          have p3143_1 := h3143c.2.1
                                          have p3143_2 := h3143c.2.2.1
                                          have p3143_3 := h3143c.2.2.2
                                          linarith only [hlam, p3143_0]
                                      · linarith only [h3104, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h1558, h3101, hlam]
                            · linarith only [h1, h3096, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            rcases p2998_3 (m.d 0 1) (by simp) with h3183 | h3183
                            · rcases p2998_3 (m.d 0 2) (by simp) with h3184 | h3184
                              · linarith only [h1385, h3184, hlam]
                              · linarith only [h1557, h3184, hlam]
                            · linarith only [h3, h3183, hlam]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h3, hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h1557, hlam, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h2828, hlam, p2998_0]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [h2829, hlam, p2998_1]
                          · have p2998_0 := h2998c.1
                            have p2998_1 := h2998c.2.1
                            have p2998_2 := h2998c.2.2.1
                            have p2998_3 := h2998c.2.2.2
                            linarith only [hlam, p2998_0]
                        · linarith only [h0, h2834, h2839, h2995, h2997, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h0, h2, h2834, h2838, h2839, h2995, h2996, h4, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2834, h2995, h4, hc25, hlam, hphi, u5elo3]
                · linarith only [h2838, hc14, hlam, hphi, ht45, u5elo4]
              · linarith only [h2837, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h2834, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h2829, hc04, hlam, hphi, ht45, u5elo4]
  · linarith only [h2828, hc03, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1558 | h1558
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1557, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1557 | h1557
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h1385 | h1385
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 6400000 in
set_option maxHeartbeats 6400000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6586000 in
set_option maxHeartbeats 6586000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3203 | h3203
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3204 | h3204
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3205 | h3205
        · linarith only [h0, h2, h3205, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3207 | h3207
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3208 | h3208
            · linarith only [h1, h2, h3208, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3210 | h3210
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3211 | h3211
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3212 | h3212
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3213 | h3213
                    · linarith only [h0, h2, h3205, h3213, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3215 | h3215
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3216 | h3216
                        · linarith only [h1, h2, h3208, h3216, hlam]
                        · linarith only [h0, h2, h3212, h3216, hc23, hc34, hlam, hphi]
                      · linarith only [h3212, h3215, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h3204, h3205, h3212, hc12, hc24, hlam, hphi]
                · linarith only [h2, h3211, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h3210, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h3204, h3207, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3224 | h3224
        · linarith only [h1, h2, h3204, h3224, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3226 | h3226
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3227 | h3227
            · linarith only [h1, h2, h3227, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3229 | h3229
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3230 | h3230
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3231 | h3231
                  · linarith only [h0, h2, h3204, h3231, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3233 | h3233
                    · linarith only [h0, h2, h3224, h3233, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3235 | h3235
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3236 | h3236
                        · linarith only [h1, h2, h3227, h3236, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3238 | h3238
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3239 | h3239
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3240 | h3240
                              · linarith only [h1, h2, h3231, h3236, h3240, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3242 | h3242
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3243 | h3243
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3244 | h3244
                                    · rcases h0bigk with h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c | h3245c
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h0, h2, h3233, h3235, h3240, h3242, h3244, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h0, h2, h3204, h3233, h3235, h3240, h3242, h3244, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h2, hlam, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        rcases p3245_3 (m.d 0 1) (by simp) with h3250 | h3250
                                        · rcases p3245_3 (m.d 0 2) (by simp) with h3251 | h3251
                                          · linarith only [h0, h3251, hlam]
                                          · linarith only [h3226, h3251, hlam]
                                        · linarith only [h3203, h3250, hlam]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h0, hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3204, hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3224, hlam, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3204, h3240, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h1, hlam, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h1, h2, h3233, h3240, hc02, hc34, hlam, hphi, ht23, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3227, hlam, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        rcases p3245_3 (m.d 0 1) (by simp) with h3264 | h3264
                                        · rcases p3245_3 (m.d 0 2) (by simp) with h3265 | h3265
                                          · linarith only [h3204, h3265, hlam]
                                          · linarith only [h3226, h3265, hlam]
                                        · linarith only [h3203, h3264, hlam]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h0, h2, h3233, h3235, h3240, h3242, h3244, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        rcases p3245_3 (m.d 0 1) (by simp) with h3270 | h3270
                                        · linarith only [h2, h3270, hlam]
                                        · linarith only [h0, h3270, hlam]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        rcases p3245_3 (m.d 0 1) (by simp) with h3273 | h3273
                                        · linarith only [h2, h3273, hlam]
                                        · linarith only [h1, h3273, hlam]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        rcases p3245_3 (m.d 0 1) (by simp) with h3277 | h3277
                                        · linarith only [h2, h3277, hlam]
                                        · linarith only [h3203, h3277, hlam]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3203, hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3226, hlam, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3229, hlam, p3245_0]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [h3230, hlam, p3245_1]
                                      · have p3245_0 := h3245c.1
                                        have p3245_1 := h3245c.2.1
                                        have p3245_2 := h3245c.2.2.1
                                        have p3245_3 := h3245c.2.2.2
                                        linarith only [hlam, p3245_0]
                                    · linarith only [h3240, h3244, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h2, h3203, h3233, h3239, h3243, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                                · linarith only [h0, h3204, h3235, h3242, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1, h2, h3231, h3235, h3239, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h3231, h3235, h3238, hc25, hlam, hphi, u5elo3]
                      · linarith only [h3235, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h3230, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h3204, h3226, h3229, hc25, hlam, hphi, u5elo3]
          · linarith only [h3226, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h3203, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

end R2N4
