import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6708000 in
set_option maxHeartbeats 6708000 in
theorem r1l7_11_25_L_0_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_25_L_0_H_I_s1 m hb1 hb5 h0 h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2844 | h2844
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2845 | h2845
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2846 | h2846
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2847 | h2847
          · linarith only [h0, h1, h2847, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2849 | h2849
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2850 | h2850
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2851 | h2851
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2852 | h2852
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2853 | h2853
                    · linarith only [h0, h1, h2847, h2850, h2853, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2855 | h2855
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2856 | h2856
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2857 | h2857
                          · linarith only [h0, h1, h2849, h2853, h2857, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2859 | h2859
                            · linarith only [h1, h2853, h2855, h2859, hc01, hc23, hlam, hphi, ht12]
                            · rcases h5bigk with h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h1, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h1, h2850, hc25, hlam, hphi, ht01, ht0b, ht5b, p2861_1, u1elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h1, h2850, h2859, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2861_1, u1elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2847, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2850, hc05, hlam, hphi, ht01, ht0b, ht5b, p2861_1, u1elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2850, hc25, hlam, hphi, ht01, ht0b, ht5b, p2861_1, u1elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2850, h2859, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2861_1, u1elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2853, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2845, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2850, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2845, h2859, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2857, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2846, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2852, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2856, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2859, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, h1, h2849, h2855, hc34, hc45, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, h1, h2849, h2855, hc34, hc45, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2856, h2859, hc34, hc45, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2859, hc34, hc45, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                        · linarith only [h2852, h2855, h2856, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h2850, h2851, h2855, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h1, h2846, h2852, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2890 | h2890
                  · linarith only [h0, h1, h2850, h2851, h2890, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h1, h2846, h2890, hlam]
              · linarith only [h1, h2845, h2850, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2894 | h2894
              · linarith only [h0, h1, h2844, h2849, h2894, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h1, h2845, h2894, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2897 | h2897
          · linarith only [h0, h1, h2897, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2899 | h2899
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2900 | h2900
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2901 | h2901
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2902 | h2902
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2903 | h2903
                    · linarith only [h0, h1, h2846, h2897, h2902, h2903, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2905 | h2905
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2906 | h2906
                        · linarith only [h2845, h2846, h2906, hlam]
                        · linarith only [h2902, h2905, h2906, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h2846, h2901, h2902, h2905, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2910 | h2910
                    · linarith only [h0, h1, h2910, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2912 | h2912
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2913 | h2913
                        · linarith only [h1, h2900, h2902, h2913, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2915 | h2915
                          · linarith only [h0, h1, h2899, h2915, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2917 | h2917
                            · linarith only [h0, h1, h2899, h2910, h2912, h2917, hlam]
                            · rcases h5bigk with h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [hlam, p2919_0]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h1, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h1, h2900, h2913, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2919_1, u1elo1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2846, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2897, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2900, hc05, hlam, hphi, ht01, ht0b, ht5b, p2919_1, u1elo1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [hlam, p2919_0]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2900, h2913, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2919_1, u1elo1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2902, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2910, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2845, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2900, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [hlam, p2919_0]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2913, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2915, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h1, hc01, hc35, hlam, hphi, ht12, ht23, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h0, h1, h2899, h2912, h2917, hc34, hc45, hlam, hphi, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2912, h2913, h2917, hc34, hc45, hlam, hphi, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [hlam, p2919_0]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2917, hlam, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h0, h1, h2899, h2912, hc34, hc45, hlam, hphi, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h0, h1, h2899, h2912, hc34, hc45, hlam, hphi, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2912, h2913, hc34, hc45, hlam, hphi, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [h2846, hc03, hc45, hlam, hphi, ht34, p2919_1]
                              · have p2919_0 := h2919c.1
                                have p2919_1 := h2919c.2.1
                                have p2919_2 := h2919c.2.2.1
                                have p2919_3 := h2919c.2.2.2
                                linarith only [hlam, p2919_0]
                      · linarith only [h0, h1, h2900, h2901, h2912, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2946 | h2946
                  · linarith only [h0, h1, h2900, h2901, h2946, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2948 | h2948
                    · linarith only [h0, h1, h2900, h2948, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2950 | h2950
                      · linarith only [h0, h1, h2899, h2900, h2901, h2950, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2952 | h2952
                        · linarith only [h1, h2946, h2950, h2952, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2954 | h2954
                          · linarith only [h0, h1, h2899, h2948, h2954, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2956 | h2956
                            · linarith only [h0, h1, h2899, h2948, h2950, h2956, hc23, hc34, hlam, hphi]
                            · rcases h5bigk with h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [hlam, p2958_0]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h1, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p2958_1, u1elo4]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2846, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2897, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2958_1, u1elo4]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [hlam, p2958_0]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2900, hc25, hlam, hphi, ht01, ht0b, ht5b, p2958_1, u1elo1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2946, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2948, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2845, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2900, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [hlam, p2958_0]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2952, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2954, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h0, h1, h2899, h2950, hc23, hc35, hlam, hphi, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h0, h1, h2899, h2950, h2956, hc23, hc45, hlam, hphi, ht34, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2952, h2956, hc23, hc45, hlam, hphi, ht34, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [hlam, p2958_0]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2956, hlam, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h0, h1, h2899, h2950, hc23, hc45, hlam, hphi, ht34, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h0, h1, h2899, h2950, hc23, hc45, hlam, hphi, ht34, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2952, hc23, hc45, hlam, hphi, ht34, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [h2846, hc03, hc45, hlam, hphi, ht34, p2958_1]
                              · have p2958_0 := h2958c.1
                                have p2958_1 := h2958c.2.1
                                have p2958_2 := h2958c.2.2.1
                                have p2958_3 := h2958c.2.2.2
                                linarith only [hlam, p2958_0]
              · linarith only [h1, h2845, h2900, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2985 | h2985
              · linarith only [h0, h1, h2844, h2899, h2985, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h1, h2845, h2985, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2988 | h2988
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2989 | h2989
          · linarith only [h0, h1, h2989, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2991 | h2991
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2992 | h2992
              · linarith only [h2844, h2845, h2992, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2994 | h2994
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2995 | h2995
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2996 | h2996
                    · linarith only [h0, h2989, h2996, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2998 | h2998
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2999 | h2999
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3000 | h3000
                          · linarith only [h0, h1, h2844, h2996, h3000, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3002 | h3002
                            · linarith only [h0, h1, h2991, h2992, h2995, h2998, h3000, h3002, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · rcases h5bigk with h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h1, hlam, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2845, hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h1, h2995, hc35, hlam, hphi, ht01, ht0b, ht5b, p3004_1, u1elo2]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2989, hlam, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2995, hc05, hlam, hphi, ht01, ht0b, ht5b, p3004_1, u1elo2]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2992, hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2995, hc35, hlam, hphi, ht01, ht0b, ht5b, p3004_1, u1elo2]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2996, hlam, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h1, hc01, hc25, hlam, hphi, ht12, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h0, h1, h2991, h2998, h3000, hc34, hc45, hlam, hphi, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h3000, h3002, hc34, hc45, hlam, hphi, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h3000, hlam, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2988, hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2995, hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2999, hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [hlam, p3004_0]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h3002, hlam, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h0, h1, h2991, h2998, hc34, hc45, hlam, hphi, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h0, h1, h2991, h2998, hc34, hc45, hlam, hphi, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h2992, hc12, hc45, hlam, hphi, ht23, ht34, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [h3002, hc34, hc45, hlam, hphi, p3004_1]
                              · have p3004_0 := h3004c.1
                                have p3004_1 := h3004c.2.1
                                have p3004_2 := h3004c.2.2.1
                                have p3004_3 := h3004c.2.2.2
                                linarith only [hlam, p3004_0]
                        · linarith only [h2995, h2998, h2999, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h2994, h2998, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h1, h2988, h2995, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3033 | h3033
                  · linarith only [h0, h1, h2994, h3033, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                  · linarith only [h1, h2988, h3033, hlam]
            · linarith only [h2844, h2845, h2991, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3037 | h3037
          · linarith only [h0, h1, h3037, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3039 | h3039
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3040 | h3040
              · linarith only [h2844, h2845, h3040, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3042 | h3042
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3043 | h3043
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3044 | h3044
                    · linarith only [h0, h1, h2988, h3037, h3043, h3044, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3046 | h3046
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3047 | h3047
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3048 | h3048
                          · linarith only [h0, h1, h2988, h3039, h3043, h3044, h3048, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3050 | h3050
                            · linarith only [h0, h1, h2844, h3040, h3046, h3048, h3050, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h5bigk with h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h1, hlam, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h2845, hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h2988, hlam, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3037, hlam, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h3039, h3046, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3052_1, u1elo4]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3040, hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h2988, h3039, h3043, h3046, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3052_1, u1elo2]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3044, hlam, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h3039, h3046, h3047, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h3039, h3046, h3048, hc34, hc45, hlam, hphi, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h2988, h3039, h3046, h3048, hc34, hc45, hlam, hphi, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3048, hlam, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h3039, h3046, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3043, hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3047, hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [hlam, p3052_0]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3050, hlam, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h3039, h3046, hc34, hc45, hlam, hphi, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h0, h1, h3039, h3046, hc34, hc45, hlam, hphi, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h3040, hc12, hc45, hlam, hphi, ht23, ht34, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [h2988, hc03, hc45, hlam, hphi, ht34, p3052_1]
                              · have p3052_0 := h3052c.1
                                have p3052_1 := h3052c.2.1
                                have p3052_2 := h3052c.2.2.1
                                have p3052_3 := h3052c.2.2.2
                                linarith only [hlam, p3052_0]
                        · linarith only [h3043, h3046, h3047, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h3042, h3046, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3080 | h3080
                    · linarith only [h0, h1, h3080, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3082 | h3082
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3083 | h3083
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3084 | h3084
                          · linarith only [h0, h1, h3039, h3080, h3084, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3086 | h3086
                            · linarith only [h0, h1, h3039, h3043, h3082, h3083, h3084, h3086, hlam]
                            · rcases h5bigk with h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h1, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h2845, hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h2988, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3037, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h1, h3043, h3083, hc01, hc23, hlam, hphi, ht12, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3040, hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3043, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3080, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3082, h3084, hc34, hc45, hlam, hphi, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3043, h3084, hc13, hc45, hlam, hphi, ht34, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3084, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3083, hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [hlam, p3088_0]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h3086, hlam, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc34, hc45, hlam, hphi, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc34, hc45, hlam, hphi, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h2845, hc02, hc45, hlam, hphi, ht23, ht34, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [h0, h1, h3039, h3043, h3082, hc34, hc45, hlam, hphi, p3088_1]
                              · have p3088_0 := h3088c.1
                                have p3088_1 := h3088c.2.1
                                have p3088_2 := h3088c.2.2.1
                                have p3088_3 := h3088c.2.2.2
                                linarith only [hlam, p3088_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3114 | h3114
                          · linarith only [h0, h1, h3039, h3114, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3116 | h3116
                            · linarith only [h0, h1, h3039, h3082, h3114, h3116, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                            · rcases h5bigk with h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [hlam, p3118_0]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h1, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h2845, hlam, p3118_0]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h2988, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3037, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, p3118_1, u1elo4]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [hlam, p3118_0]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3040, hlam, p3118_0]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3043, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3080, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [hlam, p3118_0]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3083, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3114, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3082, h3116, hc34, hc45, hlam, hphi, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3082, h3116, hc34, hc45, hlam, hphi, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h2844, h2845, h3082, h3116, hc34, hc45, hlam, hphi, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [hlam, p3118_0]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3116, hlam, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc34, hc45, hlam, hphi, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3082, hc34, hc45, hlam, hphi, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h0, h1, h3039, h3040, h3082, hc34, hc45, hlam, hphi, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [h3083, hc23, hc45, hlam, hphi, ht34, p3118_1]
                              · have p3118_0 := h3118c.1
                                have p3118_1 := h3118c.2.1
                                have p3118_2 := h3118c.2.2.1
                                have p3118_3 := h3118c.2.2.2
                                linarith only [hlam, p3118_0]
                      · linarith only [h0, h1, h3042, h3082, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3145 | h3145
                  · linarith only [h0, h1, h3042, h3145, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3147 | h3147
                    · linarith only [h0, h1, h3147, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3149 | h3149
                      · linarith only [h0, h1, h3039, h3042, h3149, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3151 | h3151
                        · linarith only [h1, h3145, h3149, h3151, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3153 | h3153
                          · linarith only [h0, h1, h3039, h3147, h3153, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3155 | h3155
                            · linarith only [h0, h1, h3039, h3040, h3149, h3153, h3155, hc23, hc34, hlam, hphi]
                            · rcases h5bigk with h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c | h3157c
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [hlam, p3157_0]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h1, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h2845, hlam, p3157_0]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h2988, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3037, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3157_1, u1elo4]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [hlam, p3157_0]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3040, hlam, p3157_0]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3145, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3147, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, h3151, h3155, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [hlam, p3157_0]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3151, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3153, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, h3155, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, h3155, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h2844, h2845, h3149, h3155, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [hlam, p3157_0]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h3155, hlam, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3149, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h0, h1, h3039, h3040, h3149, hc23, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [h2988, hc03, hc45, hlam, hphi, ht34, p3157_1]
                              · have p3157_0 := h3157c.1
                                have p3157_1 := h3157c.2.1
                                have p3157_2 := h3157c.2.2.1
                                have p3157_3 := h3157c.2.2.2
                                linarith only [hlam, p3157_0]
            · linarith only [h2844, h2845, h3039, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3184 | h3184
      · linarith only [h0, h1, h2844, h3184, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3186 | h3186
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3187 | h3187
          · linarith only [h0, h1, h3187, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3189 | h3189
            · linarith only [h0, h1, h2844, h3189, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3191 | h3191
              · linarith only [h0, h1, h3184, h3189, h3191, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3193 | h3193
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3194 | h3194
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3195 | h3195
                    · linarith only [h0, h1, h3187, h3194, h3195, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3197 | h3197
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3198 | h3198
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3199 | h3199
                          · linarith only [h0, h1, h3189, h3195, h3199, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3201 | h3201
                            · linarith only [h0, h1, h3193, h3194, h3199, h3201, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases h5bigk with h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c | h3203c
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h1, hlam, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3184, hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h1, h3194, hc35, hlam, hphi, ht01, ht0b, ht5b, p3203_1, u1elo2]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3187, hlam, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3194, hc05, hlam, hphi, ht01, ht0b, ht5b, p3203_1, u1elo2]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3191, hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3194, hc35, hlam, hphi, ht01, ht0b, ht5b, p3203_1, u1elo2]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3195, hlam, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h0, h1, h3189, hc12, hc25, hlam, hphi, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h0, h1, h3189, h3199, hc12, hc45, hlam, hphi, ht23, ht34, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3199, h3201, hc34, hc45, hlam, hphi, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3199, hlam, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3186, hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3194, hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3198, hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [hlam, p3203_0]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3201, hlam, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h0, h1, h3189, hc12, hc45, hlam, hphi, ht23, ht34, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h0, h1, h3189, hc12, hc45, hlam, hphi, ht23, ht34, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3184, hc02, hc45, hlam, hphi, ht23, ht34, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [h3201, hc34, hc45, hlam, hphi, p3203_1]
                              · have p3203_0 := h3203c.1
                                have p3203_1 := h3203c.2.1
                                have p3203_2 := h3203c.2.2.1
                                have p3203_3 := h3203c.2.2.2
                                linarith only [hlam, p3203_0]
                        · linarith only [h3194, h3197, h3198, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h3193, h3197, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h1, h3186, h3194, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3232 | h3232
                  · linarith only [h0, h1, h3193, h3232, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                  · linarith only [h1, h3186, h3232, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3235 | h3235
          · linarith only [h0, h1, h3235, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3237 | h3237
            · linarith only [h0, h2844, h3237, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3239 | h3239
              · linarith only [h3184, h3237, h3239, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3241 | h3241
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3242 | h3242
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3243 | h3243
                    · linarith only [h0, h1, h3235, h3243, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3245 | h3245
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3246 | h3246
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3247 | h3247
                          · linarith only [h0, h1, h3237, h3243, h3245, h3247, hc12, hc23, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3249 | h3249
                            · linarith only [h2844, h3247, h3249, hc02, hc34, hlam, hphi, ht23]
                            · rcases h5bigk with h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h1, hlam, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3184, hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3186, hlam, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3235, hlam, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3251_1, u1elo4]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3239, hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3186, h3237, h3242, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3251_1, u1elo2]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3243, hlam, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc25, hlam, hphi, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3237, h3247, hc12, hc45, hlam, hphi, ht23, ht34, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3186, h3237, h3247, hc12, hc45, hlam, hphi, ht23, ht34, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3247, hlam, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc35, hlam, hphi, ht23, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3242, hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3246, hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [hlam, p3251_0]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3249, hlam, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc45, hlam, hphi, ht23, ht34, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc45, hlam, hphi, ht23, ht34, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3184, hc02, hc45, hlam, hphi, ht23, ht34, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [h3186, hc03, hc45, hlam, hphi, ht34, p3251_1]
                              · have p3251_0 := h3251c.1
                                have p3251_1 := h3251c.2.1
                                have p3251_2 := h3251c.2.2.1
                                have p3251_3 := h3251c.2.2.2
                                linarith only [hlam, p3251_0]
                        · linarith only [h3242, h3245, h3246, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h3241, h3245, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3279 | h3279
                    · linarith only [h0, h1, h3279, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3281 | h3281
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3282 | h3282
                        · linarith only [h0, h1, h3237, h3242, h3282, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3284 | h3284
                          · linarith only [h0, h1, h3237, h3279, h3284, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3286 | h3286
                            · linarith only [h0, h1, h3237, h3239, h3241, h3284, h3286, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · rcases h5bigk with h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [hlam, p3288_0]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h1, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3184, hlam, p3288_0]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3186, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3235, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3288_1, u1elo4]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [hlam, p3288_0]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3239, hlam, p3288_0]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3242, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3279, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc25, hlam, hphi, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, h3282, h3286, hc12, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [hlam, p3288_0]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3282, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3284, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, h3286, hc12, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, h3286, hc12, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3184, h3286, hc02, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [hlam, p3288_0]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3286, hlam, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h0, h1, h3237, h3239, hc12, hc45, hlam, hphi, ht23, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [h3242, hc13, hc45, hlam, hphi, ht34, p3288_1]
                              · have p3288_0 := h3288c.1
                                have p3288_1 := h3288c.2.1
                                have p3288_2 := h3288c.2.2.1
                                have p3288_3 := h3288c.2.2.2
                                linarith only [hlam, p3288_0]
                      · linarith only [h0, h1, h3241, h3281, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3315 | h3315
                  · linarith only [h0, h1, h3241, h3315, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3317 | h3317
                    · linarith only [h0, h1, h3317, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3319 | h3319
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3320 | h3320
                        · linarith only [h0, h1, h3237, h3315, h3320, hc12, hc23, hlam, hphi]
                        · linarith only [h3241, h3319, h3320, hc13, hc35, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3323 | h3323
                        · linarith only [h3186, h3319, h3323, hc03, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3325 | h3325
                          · linarith only [h0, h1, h3237, h3317, h3325, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3327 | h3327
                            · linarith only [h2844, h3325, h3327, hc02, hc34, hlam, hphi, ht23]
                            · rcases h5bigk with h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h1, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3184, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3186, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3235, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3329_1, u1elo4]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3239, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3315, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3317, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, h3237, h3323, h3327, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3323, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3325, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, h3237, h3327, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, h3237, h3327, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3184, h3327, hc02, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3327, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, h3237, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, h1, h3237, h3239, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3186, hc03, hc45, hlam, hphi, ht34, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  exact r1l7_11_25_L_0_H_I_s0 m hb1 hb5 h0

end R2N4
