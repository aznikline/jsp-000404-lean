import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S2
import Jsp000404.R1LeavesN7_37S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2159 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2160 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2161 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2912 | h2912
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2913 | h2913
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2914 | h2914
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2915 | h2915
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2916 | h2916
          · linarith only [h2161, h2912, h2913, h2916, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2918 | h2918
            · linarith only [h2916, h2918, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2920 | h2920
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2921 | h2921
                · linarith only [h2158, h2916, h2920, h2921, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2923 | h2923
                  · linarith only [h0, h2158, h2923, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2925 | h2925
                    · linarith only [h0, h2159, h2925, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2927 | h2927
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
                          linarith only [h1650, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1975, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2156, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          rcases p2928_3 (m.d 0 1) (by simp) with h2934 | h2934
                          · linarith only [h2934, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 2) (by simp) with h2936 | h2936
                            · rcases p2928_3 (m.d 1 3) (by simp) with h2937 | h2937
                              · linarith only [h2913, h2937, hlam]
                              · linarith only [h1650, h2937, hlam]
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
                          linarith only [h1650, hc01, hc12, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1975, h2912, h2925, hc12, hlam, hphi, ht01, ht0b, ht5b, p2928_1, u5ehi2]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2156, h2912, h2925, hc12, hlam, hphi, ht01, ht0b, ht5b, p2928_1, u5ehi2]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2916, hc01, hc34, hlam, hphi, ht12, ht23, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2913, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2916, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2918, hlam, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          rcases p2928_3 (m.d 0 1) (by simp) with h2950 | h2950
                          · linarith only [h2950, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 2) (by simp) with h2952 | h2952
                            · rcases p2928_3 (m.d 1 3) (by simp) with h2953 | h2953
                              · linarith only [h2916, h2953, hlam]
                              · linarith only [h1650, h2953, hlam]
                            · linarith only [h0, h2952, hlam]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2914, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1650, hc01, hc14, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2156, h2912, h2916, h2925, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2928_1, u5ehi2]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          rcases p2928_3 (m.d 0 1) (by simp) with h2961 | h2961
                          · linarith only [h2961, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 2) (by simp) with h2963 | h2963
                            · rcases p2928_3 (m.d 1 3) (by simp) with h2964 | h2964
                              · linarith only [h2918, h2964, hlam]
                              · linarith only [h1650, h2964, hlam]
                            · linarith only [h0, h2963, hlam]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2915, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h1650, hc01, hc15, hlam, hphi, p2928_1]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [h2920, hlam, p2928_0]
                        · have p2928_0 := h2928c.1
                          have p2928_1 := h2928c.2.1
                          have p2928_2 := h2928c.2.2.1
                          have p2928_3 := h2928c.2.2.2
                          linarith only [hlam, p2928_0]
                      · linarith only [h2912, h2916, h2920, h2927, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h1975, h2912, h2920, hlam]
        · linarith only [h0, h2159, h2912, h2915, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · linarith only [h0, h2159, h2912, h2914, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
    · linarith only [h0, h2159, h2912, h2913, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2977 | h2977
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2978 | h2978
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2979 | h2979
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2980 | h2980
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2981 | h2981
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2982 | h2982
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2983 | h2983
                · linarith only [h0, h1650, h2158, h2161, h2983, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2985 | h2985
                  · linarith only [h2158, h2161, h2985, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2987 | h2987
                    · linarith only [h2159, h2912, h2987, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2989 | h2989
                      · linarith only [h2977, h2980, h2989, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h1650, h2161, h2977, h2980, h2982, h2989, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2992 | h2992
                · linarith only [h2158, h2161, h2992, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2994 | h2994
                  · linarith only [h2158, h2161, h2994, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2996 | h2996
                    · linarith only [h2159, h2161, h2980, h2982, h2996, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2998 | h2998
                      · linarith only [h2980, h2982, h2998, hlam]
                      · rcases h1bigk with h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h0, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h1650, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h1975, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2156, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          rcases p3000_3 (m.d 0 1) (by simp) with h3006 | h3006
                          · linarith only [h3006, hlam, p3000_0]
                          · rcases p3000_3 (m.d 1 2) (by simp) with h3008 | h3008
                            · rcases p3000_3 (m.d 1 3) (by simp) with h3009 | h3009
                              · linarith only [h2977, h3009, hlam]
                              · linarith only [h1650, h3009, hlam]
                            · linarith only [h3008, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h1650, hc01, hc12, hlam, hphi, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h1650, h2161, h2980, hc01, hc12, hlam, hphi, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3000_1, u5ehi1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          rcases p3000_3 (m.d 0 1) (by simp) with h3017 | h3017
                          · linarith only [h3017, hlam, p3000_0]
                          · rcases p3000_3 (m.d 1 2) (by simp) with h3019 | h3019
                            · rcases p3000_3 (m.d 1 3) (by simp) with h3020 | h3020
                              · rcases p3000_3 (m.d 1 4) (by simp) with h3021 | h3021
                                · linarith only [h2980, h3021, hlam]
                                · linarith only [h1975, h3021, hlam]
                              · linarith only [h3020, hlam, p3000_0]
                            · linarith only [h0, h3019, hlam]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2977, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h1650, h2161, h2980, hc01, hc13, hlam, hphi, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2156, h2160, h2977, hc12, hlam, hphi, ht01, ht0b, ht5b, p3000_1, u5ehi2]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2982, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2978, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2980, hlam, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2982, hlam, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          rcases p3000_3 (m.d 0 1) (by simp) with h3035 | h3035
                          · linarith only [h3035, hlam, p3000_0]
                          · rcases p3000_3 (m.d 1 2) (by simp) with h3037 | h3037
                            · rcases p3000_3 (m.d 1 3) (by simp) with h3038 | h3038
                              · rcases p3000_3 (m.d 1 4) (by simp) with h3039 | h3039
                                · linarith only [h2982, h3039, hlam]
                                · linarith only [h1975, h3039, hlam]
                              · linarith only [h1650, h3038, hlam]
                            · linarith only [h0, h3037, hlam]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2979, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h2981, hlam, p3000_0]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [h1975, hc01, hc15, hlam, hphi, p3000_1]
                        · have p3000_0 := h3000c.1
                          have p3000_1 := h3000c.2.1
                          have p3000_2 := h3000c.2.2.1
                          have p3000_3 := h3000c.2.2.2
                          linarith only [hlam, p3000_0]
            · linarith only [h1650, h2161, h2980, h2981, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3049 | h3049
            · linarith only [h2980, h3049, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3051 | h3051
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3052 | h3052
                · linarith only [h2980, h3051, h3052, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3054 | h3054
                  · linarith only [h2158, h2161, h2912, h3051, h3054, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3056 | h3056
                    · linarith only [h2159, h2912, h3056, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3058 | h3058
                      · rcases h1bigk with h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h0, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h1650, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h1975, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2156, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          rcases p3059_3 (m.d 0 1) (by simp) with h3065 | h3065
                          · linarith only [h3065, hlam, p3059_0]
                          · rcases p3059_3 (m.d 1 2) (by simp) with h3067 | h3067
                            · rcases p3059_3 (m.d 1 3) (by simp) with h3068 | h3068
                              · linarith only [h2977, h3068, hlam]
                              · linarith only [h1650, h3068, hlam]
                            · linarith only [h3067, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h1650, hc01, hc12, hlam, hphi, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2161, h2912, h3051, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3059_1, u5ehi1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2980, hc01, hc34, hlam, hphi, ht12, ht23, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2977, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2980, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3049, hlam, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          rcases p3059_3 (m.d 0 1) (by simp) with h3081 | h3081
                          · linarith only [h3081, hlam, p3059_0]
                          · rcases p3059_3 (m.d 1 2) (by simp) with h3083 | h3083
                            · rcases p3059_3 (m.d 1 3) (by simp) with h3084 | h3084
                              · linarith only [h2980, h3084, hlam]
                              · linarith only [h1650, h3084, hlam]
                            · linarith only [h0, h3083, hlam]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2978, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h1650, hc01, hc14, hlam, hphi, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2160, h2912, h2980, h3051, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3059_1, u5ehi2]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          rcases p3059_3 (m.d 0 1) (by simp) with h3092 | h3092
                          · linarith only [h3092, hlam, p3059_0]
                          · rcases p3059_3 (m.d 1 2) (by simp) with h3094 | h3094
                            · rcases p3059_3 (m.d 1 3) (by simp) with h3095 | h3095
                              · linarith only [h3049, h3095, hlam]
                              · linarith only [h1650, h3095, hlam]
                            · linarith only [h0, h3094, hlam]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2979, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h1650, hc01, hc15, hlam, hphi, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3051, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                      · linarith only [h1650, h2980, h3058, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3104 | h3104
                · linarith only [h1650, h2980, h3104, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3106 | h3106
                  · linarith only [h1650, h2158, h2980, h3106, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3108 | h3108
                    · linarith only [h1975, h2159, h3051, h3108, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3110 | h3110
                      · linarith only [h1975, h3051, h3110, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1650, h2980, h3110, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h2160, h2979, hlam]
      · linarith only [h0, h2160, h2978, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · linarith only [h0, h2158, h2160, h2977, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2159 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2160 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2161 | h2161
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158 h2159 h2160 h2161
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158 h2159 h2160 h2161

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2159 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2160 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h3116 | h3116
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3117 | h3117
    · linarith only [h2159, h2160, h3117, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3119 | h3119
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3120 | h3120
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3121 | h3121
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3122 | h3122
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3123 | h3123
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3124 | h3124
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3125 | h3125
                  · linarith only [h2158, h2160, h3121, h3125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h2158, h2160, h3116, h3121, h3125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3128 | h3128
                  · linarith only [h2158, h2160, h3121, h3128, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h2158, h2160, h3116, h3121, h3128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3131 | h3131
                · linarith only [h3122, h3123, h3131, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3133 | h3133
                  · linarith only [h2158, h2160, h3121, h3133, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h2158, h2160, h3116, h3121, h3133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h2158, h2160, h3116, h3121, h3122, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3137 | h3137
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3138 | h3138
              · linarith only [h3119, h3121, h3138, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3140 | h3140
                · linarith only [h3117, h3120, h3121, h3140, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3142 | h3142
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3143 | h3143
                    · linarith only [h2158, h3143, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3145 | h3145
                      · linarith only [h0, h2159, h3121, h3140, h3143, h3145, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h0, h2158, h3121, h3142, h3145, hc34, hc45, hlam, hphi]
                  · linarith only [h1650, h3116, h3138, h3142, hc23, hc35, hlam, hphi]
            · linarith only [h1650, h3116, h3137, hlam]
        · linarith only [h0, h2159, h3120, hlam]
      · linarith only [h0, h2158, h3119, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3152 | h3152
    · linarith only [h2159, h2160, h3152, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3154 | h3154
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3155 | h3155
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3156 | h3156
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3157 | h3157
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3158 | h3158
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3159 | h3159
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3160 | h3160
                  · linarith only [h1650, h2158, h2160, h3116, h3156, h3160, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3162 | h3162
                    · linarith only [h2159, h2160, h3156, h3160, h3162, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3164 | h3164
                      · linarith only [h2159, h2160, h3154, h3158, h3162, h3164, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3166 | h3166
                        · linarith only [h2159, h2160, h3160, h3164, h3166, hc23, hc34, hlam, hphi]
                        · linarith only [h1650, h3116, h3154, h3157, h3159, h3166, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3169 | h3169
                  · linarith only [h1650, h2158, h2160, h3116, h3156, h3169, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3171 | h3171
                    · linarith only [h2159, h2160, h3156, h3169, h3171, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3173 | h3173
                      · linarith only [h1650, h2159, h2160, h3116, h3154, h3157, h3158, h3159, h3171, h3173, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3175 | h3175
                        · linarith only [h3157, h3159, h3175, hlam]
                        · rcases h1bigk with h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h0, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h1650, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h1975, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h2156, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            rcases p3177_3 (m.d 0 1) (by simp) with h3183 | h3183
                            · linarith only [h3183, hlam, p3177_0]
                            · rcases p3177_3 (m.d 1 2) (by simp) with h3185 | h3185
                              · rcases p3177_3 (m.d 1 3) (by simp) with h3186 | h3186
                                · linarith only [h3154, h3186, hlam]
                                · linarith only [h1650, h3186, hlam]
                              · linarith only [h3185, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h2159, h2160, h3158, h3169, h3171, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h1650, h3116, h3157, hc01, hc12, hlam, hphi, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h2159, h2160, h3158, h3169, h3171, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            rcases p3177_3 (m.d 0 1) (by simp) with h3194 | h3194
                            · linarith only [h3194, hlam, p3177_0]
                            · rcases p3177_3 (m.d 1 2) (by simp) with h3196 | h3196
                              · rcases p3177_3 (m.d 1 3) (by simp) with h3197 | h3197
                                · rcases p3177_3 (m.d 1 4) (by simp) with h3198 | h3198
                                  · linarith only [h3157, h3198, hlam]
                                  · linarith only [h1975, h3198, hlam]
                                · linarith only [h3197, hlam, p3177_0]
                              · linarith only [h0, h3196, hlam]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3154, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h1650, h3116, h3157, hc01, hc13, hlam, hphi, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h2159, h2160, h3154, h3158, h3169, h3171, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3159, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3155, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3157, hlam, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3159, hlam, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            rcases p3177_3 (m.d 0 1) (by simp) with h3212 | h3212
                            · linarith only [h3212, hlam, p3177_0]
                            · rcases p3177_3 (m.d 1 2) (by simp) with h3214 | h3214
                              · rcases p3177_3 (m.d 1 3) (by simp) with h3215 | h3215
                                · rcases p3177_3 (m.d 1 4) (by simp) with h3216 | h3216
                                  · linarith only [h3159, h3216, hlam]
                                  · linarith only [h1975, h3216, hlam]
                                · linarith only [h1650, h3215, hlam]
                              · linarith only [h0, h3214, hlam]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3156, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h3158, hlam, p3177_0]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [h1975, hc01, hc15, hlam, hphi, p3177_1]
                          · have p3177_0 := h3177c.1
                            have p3177_1 := h3177c.2.1
                            have p3177_2 := h3177c.2.2.1
                            have p3177_3 := h3177c.2.2.2
                            linarith only [hlam, p3177_0]
              · linarith only [h1650, h3116, h3157, h3158, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3226 | h3226
              · linarith only [h3157, h3226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3228 | h3228
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3229 | h3229
                  · linarith only [h1650, h3157, h3229, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3231 | h3231
                    · linarith only [h2159, h2160, h3156, h3226, h3229, h3231, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3233 | h3233
                      · linarith only [h2159, h2160, h3152, h3156, h3233, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · linarith only [h2159, h2160, h3157, h3228, h3229, h3233, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3236 | h3236
                  · linarith only [h2158, h2160, h3156, h3236, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3238 | h3238
                    · linarith only [h2159, h2160, h3156, h3226, h3236, h3238, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3240 | h3240
                      · linarith only [h2159, h2160, h3156, h3228, h3240, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3242 | h3242
                        · linarith only [h1650, h3157, h3228, h3242, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1650, h3157, h3242, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3245 | h3245
            · linarith only [h1650, h3116, h3154, h3156, h3245, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3247 | h3247
              · linarith only [h3155, h3156, h3245, h3247, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3249 | h3249
                · linarith only [h3155, h3156, h3249, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3251 | h3251
                  · linarith only [h1650, h3245, h3251, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3253 | h3253
                    · linarith only [h1650, h2159, h3247, h3251, h3253, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3255 | h3255
                      · linarith only [h0, h2159, h3156, h3249, h3253, h3255, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3257 | h3257
                        · linarith only [h0, h2159, h3156, h3251, h3255, h3257, hc23, hc34, hlam, hphi]
                        · linarith only [h1650, h3245, h3257, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h2159, h3155, hlam]
      · linarith only [h0, h2158, h3154, hlam]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2159 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2160 | h2160
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158 h2159 h2160
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158 h2159 h2160

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2159 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3262 | h3262
  · linarith only [h2159, h3262, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3264 | h3264
    · linarith only [h2158, h2159, h3264, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3266 | h3266
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3267 | h3267
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3268 | h3268
          · linarith only [h2159, h3266, h3268, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3270 | h3270
            · linarith only [h2158, h3262, h3268, h3270, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3272 | h3272
              · linarith only [h3264, h3266, h3272, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3274 | h3274
                · linarith only [h3272, h3274, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3276 | h3276
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3277 | h3277
                    · linarith only [h0, h2158, h3268, h3272, h3277, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3279 | h3279
                      · linarith only [h1650, h3274, h3279, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3281 | h3281
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3282 | h3282
                          · rcases h1bigk with h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h0, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h1650, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h1975, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h2156, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3270, h3277, h3281, hc01, hc34, hlam, hphi, ht12, ht23, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3270, h3277, h3281, hc13, hc34, hlam, hphi, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3268, hlam, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3270, hlam, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3267, h3270, h3277, h3281, hc01, hc34, hlam, hphi, ht12, ht23, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3267, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3272, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3274, hlam, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              rcases p3283_3 (m.d 0 1) (by simp) with h3299 | h3299
                              · linarith only [h3299, hlam, p3283_0]
                              · rcases p3283_3 (m.d 1 2) (by simp) with h3301 | h3301
                                · linarith only [h3268, h3301, hlam]
                                · linarith only [h0, h3301, hlam]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h1650, h3268, h3277, hc01, hc34, hlam, hphi, ht12, ht23, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h2156, h3266, h3268, h3277, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3283_1, u5ehi4]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              rcases p3283_3 (m.d 0 1) (by simp) with h3308 | h3308
                              · linarith only [h3308, hlam, p3283_0]
                              · rcases p3283_3 (m.d 1 2) (by simp) with h3310 | h3310
                                · linarith only [h3270, h3310, hlam]
                                · linarith only [h0, h3310, hlam]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h1650, h3267, hc01, hc15, hlam, hphi, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h1650, h3274, h3282, hc01, hc34, hlam, hphi, ht12, ht23, p3283_1]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [h3276, hlam, p3283_0]
                            · have p3283_0 := h3283c.1
                              have p3283_1 := h3283c.2.1
                              have p3283_2 := h3283c.2.2.1
                              have p3283_3 := h3283c.2.2.2
                              linarith only [hlam, p3283_0]
                          · linarith only [h3266, h3268, h3276, h3277, h3282, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h1975, h3266, h3268, h3281, hlam]
                  · linarith only [h1975, h3266, h3276, hlam]
        · linarith only [h0, h2158, h3267, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3321 | h3321
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3322 | h3322
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3323 | h3323
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3324 | h3324
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3325 | h3325
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3326 | h3326
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3327 | h3327
                    · linarith only [h1650, h2158, h2159, h3264, h3266, h3321, h3324, h3326, h3327, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3329 | h3329
                      · linarith only [h2158, h2159, h3266, h3321, h3324, h3326, h3329, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3331 | h3331
                        · linarith only [h2158, h2159, h3266, h3327, h3331, hc23, hc34, hlam, hphi]
                        · linarith only [h2158, h2159, h3321, h3324, h3326, h3331, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2158, h2159, h3322, h3326, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1650, h3264, h3324, h3325, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3336 | h3336
                · linarith only [h3324, h3336, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3338 | h3338
                  · linarith only [h2158, h2159, h3266, h3324, h3338, hc23, hc34, hlam, hphi]
                  · linarith only [h2158, h2159, h3322, h3338, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2158, h2159, h3322, h3323, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3342 | h3342
            · linarith only [h3322, h3342, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3344 | h3344
              · linarith only [h1650, h3264, h3321, h3322, h3344, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3346 | h3346
                · linarith only [h3344, h3346, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3348 | h3348
                  · linarith only [h2158, h2159, h3266, h3344, h3348, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3350 | h3350
                    · linarith only [h1975, h2158, h2159, h3348, h3350, hc34, hc45, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3352 | h3352
                      · linarith only [h1975, h2158, h2159, h3346, h3348, h3352, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3354 | h3354
                        · linarith only [h2158, h2159, h3266, h3350, h3354, hc23, hc34, hlam, hphi]
                        · linarith only [h2158, h2159, h3354, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h2158, h2159, h3321, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2159 | h2159
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158 h2159
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158 h2159

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3358 | h3358
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3359 | h3359
    · linarith only [h2158, h3359, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3361 | h3361
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3362 | h3362
        · linarith only [h2158, h3358, h3362, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3364 | h3364
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3365 | h3365
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3366 | h3366
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3367 | h3367
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3368 | h3368
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3369 | h3369
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3370 | h3370
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3371 | h3371
                        · linarith only [h3364, h3371, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h2158, h3358, h3368, h3371, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2158, h3358, h3361, h3370, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3375 | h3375
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3376 | h3376
                        · linarith only [h3364, h3376, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h2158, h3358, h3364, h3368, h3375, h3376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2158, h3358, h3361, h3375, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3380 | h3380
                    · linarith only [h3362, h3367, h3368, h3380, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3382 | h3382
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3383 | h3383
                        · linarith only [h1650, h3368, h3383, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3385 | h3385
                          · linarith only [h2158, h3358, h3364, h3380, h3385, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3387 | h3387
                            · linarith only [h1975, h2158, h3358, h3364, h3368, h3380, h3382, h3387, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h2158, h3358, h3364, h3368, h3387, hc24, hc45, hlam, hphi]
                      · linarith only [h2158, h3358, h3361, h3382, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1650, h2158, h3358, h3361, h3364, h3367, hc01, hc12, hlam, hphi]
              · linarith only [h2158, h3364, h3366, hc02, hc25, hlam, hphi]
            · linarith only [h2158, h3358, h3364, h3365, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3394 | h3394
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3395 | h3395
              · linarith only [h3358, h3359, h3364, h3395, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3397 | h3397
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3398 | h3398
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3399 | h3399
                    · linarith only [h3364, h3394, h3399, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3401 | h3401
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3402 | h3402
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3403 | h3403
                          · linarith only [h3358, h3403, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3405 | h3405
                            · linarith only [h0, h3395, h3403, h3405, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h0, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h1650, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h1975, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h2156, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3395, hc01, hc25, hlam, hphi, ht12, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3364, hlam, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h1975, h3395, h3403, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3395, hlam, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                rcases p3407_3 (m.d 0 1) (by simp) with h3418 | h3418
                                · linarith only [h3418, hlam, p3407_0]
                                · rcases p3407_3 (m.d 1 2) (by simp) with h3420 | h3420
                                  · linarith only [h3364, h3420, hlam]
                                  · linarith only [h0, h3420, hlam]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h1975, h3364, hc01, hc23, hlam, hphi, ht12, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h2156, h3364, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3407_1, u5ehi0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3394, h3395, hc01, hc25, hlam, hphi, ht12, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3394, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3397, hlam, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3399, hlam, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                rcases p3407_3 (m.d 0 1) (by simp) with h3432 | h3432
                                · linarith only [h3432, hlam, p3407_0]
                                · rcases p3407_3 (m.d 1 2) (by simp) with h3434 | h3434
                                  · linarith only [h3395, h3434, hlam]
                                  · linarith only [h0, h3434, hlam]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3398, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h1975, hc01, hc15, hlam, hphi, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                        · linarith only [h3364, h3398, h3402, hlam]
                      · linarith only [h3364, h3398, h3401, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3443 | h3443
                    · linarith only [h3364, h3394, h3443, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3445 | h3445
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3446 | h3446
                        · linarith only [h0, h3364, h3398, h3446, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1975, h3364, h3394, h3446, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1975, h3364, h3394, h3445, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1650, h3361, h3397, hlam]
            · linarith only [h0, h3358, h3394, hlam]
      · linarith only [h2158, h3358, h3361, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3453 | h3453
    · linarith only [h3358, h3453, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3455 | h3455
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3456 | h3456
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3457 | h3457
          · linarith only [h2158, h3455, h3456, h3457, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3459 | h3459
            · linarith only [h3358, h3456, h3457, h3459, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3461 | h3461
              · linarith only [h3453, h3456, h3457, h3461, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3463 | h3463
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3464 | h3464
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3465 | h3465
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3466 | h3466
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3467 | h3467
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3468 | h3468
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3469 | h3469
                            · linarith only [h3455, h3469, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases h1bigk with h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h0, hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h1650, hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h1975, hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h2156, hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3461, h3466, h3468, hc01, hc23, hlam, hphi, ht12, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3457, hlam, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3459, hlam, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3461, hlam, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                rcases p3471_3 (m.d 0 1) (by simp) with h3482 | h3482
                                · linarith only [h3482, hlam, p3471_0]
                                · rcases p3471_3 (m.d 1 2) (by simp) with h3484 | h3484
                                  · linarith only [h3457, h3484, hlam]
                                  · linarith only [h0, h3484, hlam]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h0, h3457, hc01, hc23, hlam, hphi, ht12, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h1975, h3456, h3457, h3469, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3471_1, u5ehi3]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h2156, h3456, h3457, h3469, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3471_1, u5ehi3]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                rcases p3471_3 (m.d 0 1) (by simp) with h3491 | h3491
                                · linarith only [h3491, hlam, p3471_0]
                                · rcases p3471_3 (m.d 1 2) (by simp) with h3493 | h3493
                                  · linarith only [h3459, h3493, hlam]
                                  · linarith only [h0, h3493, hlam]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3463, hlam, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h2156, h3456, h3459, h3466, h3469, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3471_1, u5ehi3]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                rcases p3471_3 (m.d 0 1) (by simp) with h3500 | h3500
                                · linarith only [h3500, hlam, p3471_0]
                                · rcases p3471_3 (m.d 1 2) (by simp) with h3502 | h3502
                                  · linarith only [h3461, h3502, hlam]
                                  · linarith only [h0, h3502, hlam]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p3471_1]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3464, hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [h3465, hlam, p3471_0]
                              · have p3471_0 := h3471c.1
                                have p3471_1 := h3471c.2.1
                                have p3471_2 := h3471c.2.2.1
                                have p3471_3 := h3471c.2.2.2
                                linarith only [hlam, p3471_0]
                          · linarith only [h3456, h3459, h3465, h3468, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h1975, h3456, h3459, h3466, h3467, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h3457, h3464, h3466, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h1975, h3456, h3465, hlam]
                  · linarith only [h1650, h3455, h3456, h3464, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h1650, h3455, h3463, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3515 | h3515
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3516 | h3516
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3517 | h3517
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3518 | h3518
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3519 | h3519
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3520 | h3520
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3521 | h3521
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3522 | h3522
                        · linarith only [h3515, h3522, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h2158, h3515, h3519, h3522, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h1650, h2158, h3455, h3515, h3521, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3526 | h3526
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3527 | h3527
                        · linarith only [h3515, h3527, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h2158, h3515, h3519, h3527, hc01, hc12, hlam, hphi]
                      · linarith only [h2158, h3455, h3526, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3531 | h3531
                    · linarith only [h3456, h3518, h3519, h3531, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3533 | h3533
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3534 | h3534
                        · linarith only [h1650, h3519, h3534, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3536 | h3536
                          · linarith only [h3516, h3518, h3519, h3531, h3536, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3538 | h3538
                            · linarith only [h1975, h3531, h3538, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c | h3540c
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h0, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h1650, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h1975, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h2156, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                rcases p3540_3 (m.d 0 1) (by simp) with h3546 | h3546
                                · linarith only [h3546, hlam, p3540_0]
                                · rcases p3540_3 (m.d 1 2) (by simp) with h3548 | h3548
                                  · rcases p3540_3 (m.d 1 3) (by simp) with h3549 | h3549
                                    · linarith only [h3515, h3549, hlam]
                                    · linarith only [h1650, h3549, hlam]
                                  · linarith only [h3548, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h0, h3358, h3516, h3518, hc01, hc12, hlam, hphi, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h0, h3358, h3516, hc01, hc12, hlam, hphi, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3453, h3517, hc12, hlam, hphi, ht01, ht0b, ht5b, p3540_1, u5ehi0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3519, h3538, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3515, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h0, h3358, h3516, h3519, h3538, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3519, hlam, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3518, h3519, h3538, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3516, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3518, hlam, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3531, hlam, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                rcases p3540_3 (m.d 0 1) (by simp) with h3567 | h3567
                                · linarith only [h3567, hlam, p3540_0]
                                · rcases p3540_3 (m.d 1 2) (by simp) with h3569 | h3569
                                  · rcases p3540_3 (m.d 1 3) (by simp) with h3570 | h3570
                                    · linarith only [h3519, h3570, hlam]
                                    · linarith only [h1650, h3570, hlam]
                                  · linarith only [h0, h3569, hlam]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h3517, hlam, p3540_0]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h1650, hc01, hc15, hlam, hphi, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [h1975, h3519, h3538, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3540_1]
                              · have p3540_0 := h3540c.1
                                have p3540_1 := h3540c.2.1
                                have p3540_2 := h3540c.2.2.1
                                have p3540_3 := h3540c.2.2.2
                                linarith only [hlam, p3540_0]
                      · linarith only [h2158, h3455, h3533, hlam]
                · linarith only [h2158, h3455, h3515, h3518, hlam]
              · linarith only [h0, h2158, h3515, h3517, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2158, h3515, h3516, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3582 | h3582
            · linarith only [h0, h3358, h3515, h3582, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3584 | h3584
              · linarith only [h3515, h3584, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3586 | h3586
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3587 | h3587
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3588 | h3588
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3589 | h3589
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3590 | h3590
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3591 | h3591
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3592 | h3592
                            · linarith only [h3455, h3456, h3592, hlam]
                            · rcases h1bigk with h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h0, hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h1650, hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h1975, hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h2156, hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3584, h3589, h3591, hc01, hc23, hlam, hphi, ht12, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3515, hlam, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3582, hlam, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3584, hlam, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                rcases p3594_3 (m.d 0 1) (by simp) with h3605 | h3605
                                · linarith only [h3605, hlam, p3594_0]
                                · rcases p3594_3 (m.d 1 2) (by simp) with h3607 | h3607
                                  · linarith only [h3515, h3607, hlam]
                                  · linarith only [h0, h3607, hlam]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h0, h3515, hc01, hc23, hlam, hphi, ht12, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3456, h3515, h3588, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3515, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3594_1, u5ehi1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                rcases p3594_3 (m.d 0 1) (by simp) with h3614 | h3614
                                · linarith only [h3614, hlam, p3594_0]
                                · rcases p3594_3 (m.d 1 2) (by simp) with h3616 | h3616
                                  · linarith only [h3582, h3616, hlam]
                                  · linarith only [h0, h3616, hlam]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3586, hlam, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3582, h3588, h3589, h3592, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3594_1, u5ehi3]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                rcases p3594_3 (m.d 0 1) (by simp) with h3623 | h3623
                                · linarith only [h3623, hlam, p3594_0]
                                · rcases p3594_3 (m.d 1 2) (by simp) with h3625 | h3625
                                  · linarith only [h3584, h3625, hlam]
                                  · linarith only [h0, h3625, hlam]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p3594_1]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3587, hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [h3588, hlam, p3594_0]
                              · have p3594_0 := h3594c.1
                                have p3594_1 := h3594c.2.1
                                have p3594_2 := h3594c.2.2.1
                                have p3594_3 := h3594c.2.2.2
                                linarith only [hlam, p3594_0]
                          · linarith only [h0, h3582, h3591, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h3515, h3590, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3456, h3515, h3586, h3588, h3589, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3635 | h3635
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3636 | h3636
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3637 | h3637
                          · linarith only [h1975, h3588, h3637, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h3582, h3637, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h3515, h3587, h3636, hlam]
                      · linarith only [h3455, h3515, h3587, h3635, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3642 | h3642
                    · linarith only [h3586, h3587, h3642, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3644 | h3644
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3645 | h3645
                        · linarith only [h1650, h3587, h3645, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3515, h3645, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h3455, h3515, h3644, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h1650, h3455, h3586, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3650 | h3650
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3651 | h3651
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3652 | h3652
            · linarith only [h3358, h3650, h3652, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h2158, h3651, h3652, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3655 | h3655
            · linarith only [h0, h3358, h3651, h3655, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3657 | h3657
              · linarith only [h3651, h3657, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3659 | h3659
                · linarith only [h3455, h3650, h3659, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3661 | h3661
                  · linarith only [h3659, h3661, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3663 | h3663
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3664 | h3664
                      · linarith only [h0, h3651, h3659, h3664, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3651, h3664, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1975, h3650, h3663, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3668 | h3668
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3669 | h3669
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3670 | h3670
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3671 | h3671
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3672 | h3672
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3673 | h3673
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3674 | h3674
                      · linarith only [h0, h2158, h3455, h3668, h3674, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2158, h3668, h3671, h3674, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3677 | h3677
                      · linarith only [h0, h2158, h3455, h3668, h3677, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2158, h3671, h3673, h3677, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h2158, h3455, h3671, h3672, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3681 | h3681
                  · linarith only [h3671, h3681, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3683 | h3683
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3684 | h3684
                      · linarith only [h1650, h3671, h3684, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3686 | h3686
                        · linarith only [h3668, h3681, h3686, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3688 | h3688
                          · linarith only [h0, h2158, h3455, h3650, h3669, h3688, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h3358, h3683, h3688, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3691 | h3691
                      · linarith only [h0, h2158, h3455, h3668, h3681, h3691, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3693 | h3693
                        · linarith only [h1650, h3681, h3691, h3693, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3695 | h3695
                          · linarith only [h3669, h3683, h3695, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3697 | h3697
                            · linarith only [h1975, h3683, h3697, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2158, h3668, h3671, h3697, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h2158, h3668, h3670, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2158, h3668, h3669, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3702 | h3702
            · linarith only [h0, h3358, h3668, h3702, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3704 | h3704
              · linarith only [h3668, h3704, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3706 | h3706
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3707 | h3707
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3708 | h3708
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3709 | h3709
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3710 | h3710
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3711 | h3711
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3712 | h3712
                            · linarith only [h0, h2158, h3455, h3650, h3706, h3712, hc01, hc13, hlam, hphi]
                            · linarith only [h0, h2158, h3455, h3708, h3712, hc01, hc14, hlam, hphi]
                          · linarith only [h3702, h3708, h3711, hlam]
                        · linarith only [h3668, h3707, h3710, hlam]
                      · linarith only [h3668, h3707, h3709, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3718 | h3718
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3719 | h3719
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3720 | h3720
                          · linarith only [h1975, h3708, h3720, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h3702, h3720, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h3668, h3707, h3719, hlam]
                      · linarith only [h3668, h3706, h3707, h3718, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h2158, h3455, h3706, h3707, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3726 | h3726
                  · linarith only [h3706, h3726, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3728 | h3728
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3729 | h3729
                      · linarith only [h1650, h3706, h3729, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3668, h3729, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3732 | h3732
                      · linarith only [h0, h3668, h3706, h3732, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3668, h3732, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2158 | h2158
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156 h2158

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2156 | h2156
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1650 h1975 h2156

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1975 | h1975
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1650 h1975
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1650 h1975

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1650 | h1650
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x0 m hb1 hb2 hb4 hb5 h0 h1650
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1 m hb1 hb2 hb4 hb5 h0 h1650

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
