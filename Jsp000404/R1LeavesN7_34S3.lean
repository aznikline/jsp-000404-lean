import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 1 2 3 (by decide) (by decide) with h2909 | h2909
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2910 | h2910
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2911 | h2911
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2912 | h2912
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2913 | h2913
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2914 | h2914
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2915 | h2915
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2916 | h2916
                · linarith only [h2079, h2083, h2916, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2918 | h2918
                  · linarith only [h2079, h2083, h2914, h2918, hlam]
                  · rcases h0bigk with h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h0, hlam, p2920_1]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h1265, hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h1561, h2079, h2083, h2909, h2911, h2913, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2920_1, u2ehi3]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h1561, hlam, p2920_1]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h2926 | h2926
                      · linarith only [h0, h2926, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h2928 | h2928
                        · rcases p2920_3 (m.d 0 3) (by simp) with h2929 | h2929
                          · linarith only [h2078, h2929, hlam]
                          · linarith only [h1265, h2929, hlam]
                        · linarith only [h0, h2928, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h2934 | h2934
                      · linarith only [h0, h2934, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h2936 | h2936
                        · rcases p2920_3 (m.d 0 3) (by simp) with h2937 | h2937
                          · linarith only [h2078, h2937, hlam]
                          · rcases p2920_3 (m.d 0 4) (by simp) with h2939 | h2939
                            · linarith only [h2079, h2939, hlam]
                            · rcases p2920_3 (m.d 0 5) (by simp) with h2941 | h2941
                              · linarith only [h2080, h2941, hlam]
                              · rcases h3bigk with h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h1265, hlam, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2920_1, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2920_1, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h0, h2918, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2920_1, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h1561, h2082, h2909, hc01, hc12, hlam, hphi, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2909, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2943_1, u2ehi2]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  rcases p2943_3 (m.d 0 3) (by simp) with h2952 | h2952
                                  · linarith only [h1265, h2952, hlam]
                                  · linarith only [h2081, h2952, hlam]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  rcases p2943_3 (m.d 0 3) (by simp) with h2955 | h2955
                                  · linarith only [h1265, h2955, hlam]
                                  · linarith only [h2082, h2955, hlam]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2078, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2909, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h0, h2078, h2918, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2920_1, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2081, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2911, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2914, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2918, hlam, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2082, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2912, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h2915, hlam, p2943_0]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [h0, h2082, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2920_1, p2943_1]
                                · have p2943_0 := h2943c.1
                                  have p2943_1 := h2943c.2.1
                                  have p2943_2 := h2943c.2.2.1
                                  have p2943_3 := h2943c.2.2.2
                                  linarith only [hlam, p2943_0]
                        · linarith only [h2078, h2936, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h2974 | h2974
                      · linarith only [h0, h2974, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h2976 | h2976
                        · rcases p2920_3 (m.d 0 3) (by simp) with h2977 | h2977
                          · linarith only [h2078, h2977, hlam]
                          · linarith only [h2081, h2977, hlam]
                        · linarith only [h2079, h2976, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h2981 | h2981
                      · linarith only [h0, h2981, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h2983 | h2983
                        · rcases p2920_3 (m.d 0 3) (by simp) with h2984 | h2984
                          · linarith only [h2078, h2984, hlam]
                          · linarith only [h2082, h2984, hlam]
                        · linarith only [h2080, h2983, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h2988 | h2988
                      · linarith only [h1265, h2988, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h2990 | h2990
                        · rcases p2920_3 (m.d 0 3) (by simp) with h2991 | h2991
                          · rcases p2920_3 (m.d 0 4) (by simp) with h2992 | h2992
                            · linarith only [h2081, h2992, hlam]
                            · rcases p2920_3 (m.d 0 5) (by simp) with h2994 | h2994
                              · linarith only [h2082, h2994, hlam]
                              · linarith only [h1561, h2994, hlam]
                          · linarith only [h1265, h2991, hlam]
                        · linarith only [h0, h2990, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2078, hlam, p2920_1]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h3001 | h3001
                      · linarith only [h1265, h3001, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h3003 | h3003
                        · rcases p2920_3 (m.d 0 3) (by simp) with h3004 | h3004
                          · rcases p2920_3 (m.d 0 4) (by simp) with h3005 | h3005
                            · linarith only [h2081, h3005, hlam]
                            · rcases p2920_3 (m.d 0 5) (by simp) with h3007 | h3007
                              · linarith only [h2082, h3007, hlam]
                              · linarith only [h2083, h3007, hlam]
                          · linarith only [h2081, h3004, hlam]
                        · linarith only [h2079, h3003, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      rcases p2920_3 (m.d 0 1) (by simp) with h3012 | h3012
                      · linarith only [h1265, h3012, hlam]
                      · rcases p2920_3 (m.d 0 2) (by simp) with h3014 | h3014
                        · rcases p2920_3 (m.d 0 3) (by simp) with h3015 | h3015
                          · rcases p2920_3 (m.d 0 4) (by simp) with h3016 | h3016
                            · linarith only [h2081, h3016, hlam]
                            · rcases p2920_3 (m.d 0 5) (by simp) with h3018 | h3018
                              · linarith only [h2082, h3018, hlam]
                              · rcases h3bigk with h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h1265, hlam, p3020_1]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h1265, h2909, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3020_1, u2ehi2]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  rcases p3020_3 (m.d 0 3) (by simp) with h3024 | h3024
                                  · rcases p3020_3 (m.d 1 3) (by simp) with h3025 | h3025
                                    · rcases p3020_3 (m.d 2 3) (by simp) with h3026 | h3026
                                      · linarith only [h2078, h3026, hlam]
                                      · linarith only [h2914, h3026, hlam]
                                    · linarith only [h2911, h3025, hlam]
                                  · linarith only [h3024, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  rcases p3020_3 (m.d 0 3) (by simp) with h3031 | h3031
                                  · rcases p3020_3 (m.d 1 3) (by simp) with h3032 | h3032
                                    · rcases p3020_3 (m.d 2 3) (by simp) with h3033 | h3033
                                      · linarith only [h2078, h3033, hlam]
                                      · linarith only [h2915, h3033, hlam]
                                    · linarith only [h2912, h3032, hlam]
                                  · linarith only [h3031, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2909, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2920_1, p3020_1]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2909, h2915, h2916, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3020_1, u2ehi3]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  rcases p3020_3 (m.d 0 3) (by simp) with h3041 | h3041
                                  · linarith only [h1265, h3041, hlam]
                                  · linarith only [h2081, h3041, hlam]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  rcases p3020_3 (m.d 0 3) (by simp) with h3044 | h3044
                                  · linarith only [h1265, h3044, hlam]
                                  · linarith only [h2082, h3044, hlam]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2078, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2909, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3020_1]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h0, h2078, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3020_1]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2081, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2911, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2914, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2918, hlam, p3020_1]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2082, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2912, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2915, hlam, p3020_0]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [h2082, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3020_1]
                                · have p3020_0 := h3020c.1
                                  have p3020_1 := h3020c.2.1
                                  have p3020_2 := h3020c.2.2.1
                                  have p3020_3 := h3020c.2.2.2
                                  linarith only [hlam, p3020_0]
                          · linarith only [h2082, h3015, hlam]
                        · linarith only [h2080, h3014, hlam]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2083, h2909, h2911, h2913, hc01, hc12, hlam, hphi, p2920_1]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2079, hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2081, hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2083, hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2083, h2909, h2911, h2913, hc01, hc12, hlam, hphi, p2920_1]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2080, hlam, p2920_1]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2082, hlam, p2920_0]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [h2079, h2083, h2909, h2911, h2913, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2920_1, u2ehi3]
                    · have p2920_0 := h2920c.1
                      have p2920_1 := h2920c.2.1
                      have p2920_2 := h2920c.2.2.1
                      have p2920_3 := h2920c.2.2.2
                      linarith only [hlam, p2920_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3074 | h3074
                · linarith only [h2082, h2083, h2915, h3074, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3076 | h3076
                  · linarith only [h2082, h2083, h2914, h2915, h3076, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases h0bigk with h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h0, hlam, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h1265, hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h0, h2079, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3078_1, u2ehi3]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h1561, hlam, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      rcases p3078_3 (m.d 0 1) (by simp) with h3084 | h3084
                      · linarith only [h0, h3084, hlam]
                      · rcases p3078_3 (m.d 0 2) (by simp) with h3086 | h3086
                        · rcases p3078_3 (m.d 0 3) (by simp) with h3087 | h3087
                          · linarith only [h2078, h3087, hlam]
                          · linarith only [h1265, h3087, hlam]
                        · linarith only [h0, h3086, hlam]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h0, h2082, h2915, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      rcases p3078_3 (m.d 0 1) (by simp) with h3093 | h3093
                      · linarith only [h0, h3093, hlam]
                      · rcases p3078_3 (m.d 0 2) (by simp) with h3095 | h3095
                        · rcases p3078_3 (m.d 0 3) (by simp) with h3096 | h3096
                          · linarith only [h2078, h3096, hlam]
                          · linarith only [h2081, h3096, hlam]
                        · linarith only [h2079, h3095, hlam]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h0, h2082, h2914, h2915, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3078_1, u2ehi3]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      rcases p3078_3 (m.d 0 1) (by simp) with h3101 | h3101
                      · linarith only [h1265, h3101, hlam]
                      · rcases p3078_3 (m.d 0 2) (by simp) with h3103 | h3103
                        · rcases p3078_3 (m.d 0 3) (by simp) with h3104 | h3104
                          · rcases p3078_3 (m.d 0 4) (by simp) with h3105 | h3105
                            · linarith only [h2081, h3105, hlam]
                            · rcases p3078_3 (m.d 0 5) (by simp) with h3107 | h3107
                              · linarith only [h2082, h3107, hlam]
                              · linarith only [h1561, h3107, hlam]
                          · linarith only [h1265, h3104, hlam]
                        · linarith only [h0, h3103, hlam]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2078, hlam, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      rcases p3078_3 (m.d 0 1) (by simp) with h3114 | h3114
                      · linarith only [h1265, h3114, hlam]
                      · rcases p3078_3 (m.d 0 2) (by simp) with h3116 | h3116
                        · rcases p3078_3 (m.d 0 3) (by simp) with h3117 | h3117
                          · rcases p3078_3 (m.d 0 4) (by simp) with h3118 | h3118
                            · linarith only [h2081, h3118, hlam]
                            · rcases p3078_3 (m.d 0 5) (by simp) with h3120 | h3120
                              · linarith only [h2082, h3120, hlam]
                              · linarith only [h2083, h3120, hlam]
                          · linarith only [h2081, h3117, hlam]
                        · linarith only [h2079, h3116, hlam]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2082, h2914, h2915, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3078_1, u2ehi3]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2083, h2909, h2911, h2913, hc01, hc12, hlam, hphi, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2079, hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2081, hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2083, hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2083, h2909, h2911, h2913, hc01, hc12, hlam, hphi, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2080, hlam, p3078_1]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2082, hlam, p3078_0]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [h2079, h2083, h2909, h2911, h2913, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3078_1, u2ehi3]
                    · have p3078_0 := h3078c.1
                      have p3078_1 := h3078c.2.1
                      have p3078_2 := h3078c.2.2.1
                      have p3078_3 := h3078c.2.2.2
                      linarith only [hlam, p3078_0]
            · linarith only [h2081, h2083, h2909, h2911, h2913, h2914, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3137 | h3137
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3138 | h3138
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3139 | h3139
                · linarith only [h0, h1561, h2078, h2913, h3137, h3139, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3141 | h3141
                  · linarith only [h2079, h2083, h3141, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases h0bigk with h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h0, hlam, p3143_1]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h1265, hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h0, h2079, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3143_1, u2ehi3]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h1561, hlam, p3143_1]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3149 | h3149
                      · linarith only [h0, h3149, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3151 | h3151
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3152 | h3152
                          · linarith only [h2078, h3152, hlam]
                          · linarith only [h1265, h3152, hlam]
                        · linarith only [h0, h3151, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3157 | h3157
                      · linarith only [h0, h3157, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3159 | h3159
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3160 | h3160
                          · linarith only [h2078, h3160, hlam]
                          · rcases p3143_3 (m.d 0 4) (by simp) with h3162 | h3162
                            · linarith only [h2079, h3162, hlam]
                            · rcases p3143_3 (m.d 0 5) (by simp) with h3164 | h3164
                              · linarith only [h2080, h3164, hlam]
                              · rcases h3bigk with h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h1265, hlam, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3143_1, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3143_1, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h0, h3141, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3143_1, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h1265, h2909, hc01, hc12, hlam, hphi, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2909, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3166_1, u2ehi2]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  rcases p3166_3 (m.d 0 3) (by simp) with h3175 | h3175
                                  · linarith only [h1265, h3175, hlam]
                                  · linarith only [h2081, h3175, hlam]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  rcases p3166_3 (m.d 0 3) (by simp) with h3178 | h3178
                                  · linarith only [h1265, h3178, hlam]
                                  · linarith only [h2082, h3178, hlam]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2078, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2909, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h0, h2078, h3141, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3143_1, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2081, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2911, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h3137, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h3141, hlam, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2082, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h2912, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h3138, hlam, p3166_0]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [h0, h2082, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3143_1, p3166_1]
                                · have p3166_0 := h3166c.1
                                  have p3166_1 := h3166c.2.1
                                  have p3166_2 := h3166c.2.2.1
                                  have p3166_3 := h3166c.2.2.2
                                  linarith only [hlam, p3166_0]
                        · linarith only [h2078, h3159, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3197 | h3197
                      · linarith only [h0, h3197, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3199 | h3199
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3200 | h3200
                          · linarith only [h2078, h3200, hlam]
                          · linarith only [h2081, h3200, hlam]
                        · linarith only [h2079, h3199, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3204 | h3204
                      · linarith only [h0, h3204, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3206 | h3206
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3207 | h3207
                          · linarith only [h2078, h3207, hlam]
                          · linarith only [h2082, h3207, hlam]
                        · linarith only [h2080, h3206, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3211 | h3211
                      · linarith only [h1265, h3211, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3213 | h3213
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3214 | h3214
                          · rcases p3143_3 (m.d 0 4) (by simp) with h3215 | h3215
                            · linarith only [h2081, h3215, hlam]
                            · rcases p3143_3 (m.d 0 5) (by simp) with h3217 | h3217
                              · linarith only [h2082, h3217, hlam]
                              · linarith only [h1561, h3217, hlam]
                          · linarith only [h1265, h3214, hlam]
                        · linarith only [h0, h3213, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2078, hlam, p3143_1]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3224 | h3224
                      · linarith only [h1265, h3224, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3226 | h3226
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3227 | h3227
                          · rcases p3143_3 (m.d 0 4) (by simp) with h3228 | h3228
                            · linarith only [h2081, h3228, hlam]
                            · rcases p3143_3 (m.d 0 5) (by simp) with h3230 | h3230
                              · linarith only [h2082, h3230, hlam]
                              · linarith only [h2083, h3230, hlam]
                          · linarith only [h2081, h3227, hlam]
                        · linarith only [h2079, h3226, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3235 | h3235
                      · linarith only [h1265, h3235, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3237 | h3237
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3238 | h3238
                          · rcases p3143_3 (m.d 0 4) (by simp) with h3239 | h3239
                            · linarith only [h2081, h3239, hlam]
                            · rcases p3143_3 (m.d 0 5) (by simp) with h3241 | h3241
                              · linarith only [h2082, h3241, hlam]
                              · rcases h3bigk with h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c | h3243c
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h1265, hlam, p3243_1]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3243_1, u2ehi2]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  rcases p3243_3 (m.d 0 3) (by simp) with h3247 | h3247
                                  · rcases p3243_3 (m.d 1 3) (by simp) with h3248 | h3248
                                    · rcases p3243_3 (m.d 2 3) (by simp) with h3249 | h3249
                                      · linarith only [h2078, h3249, hlam]
                                      · linarith only [h3137, h3249, hlam]
                                    · linarith only [h2911, h3248, hlam]
                                  · linarith only [h3247, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  rcases p3243_3 (m.d 0 3) (by simp) with h3254 | h3254
                                  · rcases p3243_3 (m.d 1 3) (by simp) with h3255 | h3255
                                    · rcases p3243_3 (m.d 2 3) (by simp) with h3256 | h3256
                                      · linarith only [h2078, h3256, hlam]
                                      · linarith only [h3138, h3256, hlam]
                                    · linarith only [h2912, h3255, hlam]
                                  · linarith only [h3254, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h1265, h2909, hc01, hc12, hlam, hphi, p3243_1]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2909, h3138, h3139, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3243_1, u2ehi3]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  rcases p3243_3 (m.d 0 3) (by simp) with h3264 | h3264
                                  · linarith only [h1265, h3264, hlam]
                                  · linarith only [h2081, h3264, hlam]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  rcases p3243_3 (m.d 0 3) (by simp) with h3267 | h3267
                                  · linarith only [h1265, h3267, hlam]
                                  · linarith only [h2082, h3267, hlam]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2078, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2909, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3243_1]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h0, h2078, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3243_1]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2081, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2911, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h3137, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h3141, hlam, p3243_1]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2082, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2912, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h3138, hlam, p3243_0]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [h2082, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3243_1]
                                · have p3243_0 := h3243c.1
                                  have p3243_1 := h3243c.2.1
                                  have p3243_2 := h3243c.2.2.1
                                  have p3243_3 := h3243c.2.2.2
                                  linarith only [hlam, p3243_0]
                          · linarith only [h2082, h3238, hlam]
                        · linarith only [h2080, h3237, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2083, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3143_1]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2079, hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2081, hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2083, hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      rcases p3143_3 (m.d 0 1) (by simp) with h3292 | h3292
                      · linarith only [h1561, h3292, hlam]
                      · rcases p3143_3 (m.d 0 2) (by simp) with h3294 | h3294
                        · rcases p3143_3 (m.d 0 3) (by simp) with h3295 | h3295
                          · rcases p3143_3 (m.d 0 4) (by simp) with h3296 | h3296
                            · linarith only [h2083, h3296, hlam]
                            · linarith only [h2079, h2083, h3296, hc45, hlam, hphi, ht23, ht34, p3143_1, u2ehi3]
                          · linarith only [h1265, h3295, hlam]
                        · linarith only [h0, h3294, hlam]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2080, hlam, p3143_1]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2082, hlam, p3143_0]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [h2079, h2083, hc45, hlam, hphi, ht23, ht34, p3143_1, u2ehi3]
                    · have p3143_0 := h3143c.1
                      have p3143_1 := h3143c.2.1
                      have p3143_2 := h3143c.2.2.1
                      have p3143_3 := h3143c.2.2.2
                      linarith only [hlam, p3143_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3305 | h3305
                · linarith only [h0, h1561, h2079, h2913, h3305, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3307 | h3307
                  · linarith only [h1561, h2082, h2913, h3137, h3138, h3307, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases h0bigk with h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c | h3309c
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h0, hlam, p3309_1]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h1265, hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h1561, h2913, hc04, hc45, hlam, hphi, p3309_1]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h1561, hlam, p3309_1]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      rcases p3309_3 (m.d 0 1) (by simp) with h3315 | h3315
                      · linarith only [h0, h3315, hlam]
                      · rcases p3309_3 (m.d 0 2) (by simp) with h3317 | h3317
                        · rcases p3309_3 (m.d 0 3) (by simp) with h3318 | h3318
                          · linarith only [h2078, h3318, hlam]
                          · linarith only [h1265, h3318, hlam]
                        · linarith only [h0, h3317, hlam]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h0, h2082, h3137, h3138, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3309_1, u2ehi3]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      rcases p3309_3 (m.d 0 1) (by simp) with h3324 | h3324
                      · linarith only [h0, h3324, hlam]
                      · rcases p3309_3 (m.d 0 2) (by simp) with h3326 | h3326
                        · rcases p3309_3 (m.d 0 3) (by simp) with h3327 | h3327
                          · linarith only [h2078, h3327, hlam]
                          · linarith only [h2081, h3327, hlam]
                        · linarith only [h2079, h3326, hlam]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h0, h2082, h3137, h3138, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3309_1, u2ehi3]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      rcases p3309_3 (m.d 0 1) (by simp) with h3332 | h3332
                      · linarith only [h1265, h3332, hlam]
                      · rcases p3309_3 (m.d 0 2) (by simp) with h3334 | h3334
                        · rcases p3309_3 (m.d 0 3) (by simp) with h3335 | h3335
                          · rcases p3309_3 (m.d 0 4) (by simp) with h3336 | h3336
                            · linarith only [h2081, h3336, hlam]
                            · rcases p3309_3 (m.d 0 5) (by simp) with h3338 | h3338
                              · linarith only [h2082, h3338, hlam]
                              · linarith only [h1561, h3338, hlam]
                          · linarith only [h1265, h3335, hlam]
                        · linarith only [h0, h3334, hlam]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2078, hlam, p3309_1]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      rcases p3309_3 (m.d 0 1) (by simp) with h3345 | h3345
                      · linarith only [h1265, h3345, hlam]
                      · rcases p3309_3 (m.d 0 2) (by simp) with h3347 | h3347
                        · rcases p3309_3 (m.d 0 3) (by simp) with h3348 | h3348
                          · rcases p3309_3 (m.d 0 4) (by simp) with h3349 | h3349
                            · linarith only [h2081, h3349, hlam]
                            · rcases p3309_3 (m.d 0 5) (by simp) with h3351 | h3351
                              · linarith only [h2082, h3351, hlam]
                              · linarith only [h2083, h3351, hlam]
                          · linarith only [h2081, h3348, hlam]
                        · linarith only [h2079, h3347, hlam]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2082, h3137, h3138, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3309_1, u2ehi3]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2083, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3309_1]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2079, hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2081, hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2083, hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      rcases p3309_3 (m.d 0 1) (by simp) with h3362 | h3362
                      · linarith only [h1561, h3362, hlam]
                      · rcases p3309_3 (m.d 0 2) (by simp) with h3364 | h3364
                        · rcases p3309_3 (m.d 0 3) (by simp) with h3365 | h3365
                          · rcases p3309_3 (m.d 0 4) (by simp) with h3366 | h3366
                            · linarith only [h2083, h3366, hlam]
                            · linarith only [h1561, h2079, h2913, h3366, hc45, hlam, hphi, ht23, ht34, p3309_1, u2ehi3]
                          · linarith only [h1265, h3365, hlam]
                        · linarith only [h0, h3364, hlam]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2080, hlam, p3309_1]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h2082, hlam, p3309_0]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [h1561, h2079, h2913, hc45, hlam, hphi, ht23, ht34, p3309_1, u2ehi3]
                    · have p3309_0 := h3309c.1
                      have p3309_1 := h3309c.2.1
                      have p3309_2 := h3309c.2.2.1
                      have p3309_3 := h3309c.2.2.2
                      linarith only [hlam, p3309_0]
            · linarith only [h2081, h2083, h3137, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h1265, h2082, h2912, hlam]
      · linarith only [h1265, h2081, h2083, h2911, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
    · linarith only [h0, h2078, h2910, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h2080, h2909, hc23, hlam, hphi, u2ehi4]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 4 5 (by decide) (by decide) with h2083 | h2083
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 4 5 (by decide) (by decide) with h3380 | h3380
  · linarith only [h2081, h2082, h3380, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3382 | h3382
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3383 | h3383
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3384 | h3384
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3385 | h3385
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3386 | h3386
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3387 | h3387
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3388 | h3388
                · linarith only [h0, h1265, h2078, h2082, h3388, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3390 | h3390
                  · linarith only [h2079, h3380, h3390, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3392 | h3392
                    · linarith only [h2079, h3380, h3387, h3392, hc23, hlam, hphi, u2ehi3]
                    · rcases h0bigk with h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h0, hlam, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h1265, hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h1265, h2079, h2082, h3384, h3386, h3392, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3394_1, u2ehi3]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h1561, hlam, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        rcases p3394_3 (m.d 0 1) (by simp) with h3400 | h3400
                        · linarith only [h0, h3400, hlam]
                        · rcases p3394_3 (m.d 0 2) (by simp) with h3402 | h3402
                          · rcases p3394_3 (m.d 0 3) (by simp) with h3403 | h3403
                            · linarith only [h2078, h3403, hlam]
                            · linarith only [h1265, h3403, hlam]
                          · linarith only [h0, h3402, hlam]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        rcases p3394_3 (m.d 0 1) (by simp) with h3408 | h3408
                        · linarith only [h0, h3408, hlam]
                        · rcases p3394_3 (m.d 0 2) (by simp) with h3410 | h3410
                          · rcases p3394_3 (m.d 0 3) (by simp) with h3411 | h3411
                            · linarith only [h2078, h3411, hlam]
                            · rcases p3394_3 (m.d 0 4) (by simp) with h3413 | h3413
                              · linarith only [h2079, h3413, hlam]
                              · rcases p3394_3 (m.d 0 5) (by simp) with h3415 | h3415
                                · linarith only [h2080, h3415, hlam]
                                · linarith only [h2082, h3415, hlam]
                          · linarith only [h2078, h3410, hlam]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        rcases p3394_3 (m.d 0 1) (by simp) with h3419 | h3419
                        · linarith only [h0, h3419, hlam]
                        · rcases p3394_3 (m.d 0 2) (by simp) with h3421 | h3421
                          · rcases p3394_3 (m.d 0 3) (by simp) with h3422 | h3422
                            · linarith only [h2078, h3422, hlam]
                            · linarith only [h2081, h3422, hlam]
                          · linarith only [h2079, h3421, hlam]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        rcases p3394_3 (m.d 0 1) (by simp) with h3426 | h3426
                        · linarith only [h0, h3426, hlam]
                        · rcases p3394_3 (m.d 0 2) (by simp) with h3428 | h3428
                          · rcases p3394_3 (m.d 0 3) (by simp) with h3429 | h3429
                            · linarith only [h2078, h3429, hlam]
                            · rcases p3394_3 (m.d 0 4) (by simp) with h3431 | h3431
                              · linarith only [h2079, h3431, hlam]
                              · rcases p3394_3 (m.d 0 5) (by simp) with h3433 | h3433
                                · linarith only [h2080, h3433, hlam]
                                · rcases h3bigk with h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c | h3435c
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h1265, hlam, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2082, h3382, h3384, h3386, h3392, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2082, h3382, h3384, h3386, h3392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2082, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h1265, h3382, hc01, hc12, hlam, hphi, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3382, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3435_1, u2ehi2]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    rcases p3435_3 (m.d 0 3) (by simp) with h3444 | h3444
                                    · linarith only [h1265, h3444, hlam]
                                    · linarith only [h2081, h3444, hlam]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2079, h2081, h2082, h3382, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3435_1, u2ehi3]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2078, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3382, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3388, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2081, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3384, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3387, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3392, hlam, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h2079, h2081, hc35, hlam, hphi, ht23, p3435_1, u2ehi3]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3385, hlam, p3435_0]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3382, h3385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [h3382, h3384, h3386, h3392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3435_1]
                                  · have p3435_0 := h3435c.1
                                    have p3435_1 := h3435c.2.1
                                    have p3435_2 := h3435c.2.2.1
                                    have p3435_3 := h3435c.2.2.2
                                    linarith only [hlam, p3435_0]
                          · linarith only [h2080, h3428, hlam]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2082, h3382, h3384, h3386, h3392, hc01, hc12, hlam, hphi, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2078, hlam, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2079, h2082, h3382, h3384, h3386, h3392, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3394_1, u2ehi3]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2082, hlam, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2081, h2082, h3382, h3384, h3386, h3392, hc01, hc12, hlam, hphi, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2079, hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2081, hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h3380, hlam, p3394_0]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2082, h3382, h3384, h3386, h3392, hc01, hc12, hlam, hphi, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2080, hlam, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h1265, h2082, h3382, h3384, h3386, h3392, hc01, hc12, hlam, hphi, p3394_1]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [h2079, h2082, h3382, h3384, h3386, h3392, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3394_1, u2ehi3]
                      · have p3394_0 := h3394c.1
                        have p3394_1 := h3394c.2.1
                        have p3394_2 := h3394c.2.2.1
                        have p3394_3 := h3394c.2.2.2
                        linarith only [hlam, p3394_0]
              · linarith only [h2081, h2082, h3387, hc23, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3480 | h3480
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3481 | h3481
                · linarith only [h2078, h2082, h3481, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3483 | h3483
                  · linarith only [h2079, h2081, h2082, h3382, h3385, h3386, h3483, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3485 | h3485
                    · linarith only [h2078, h2082, h3385, h3386, h3480, h3485, hlam]
                    · rcases h0bigk with h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h0, hlam, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h1265, hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h0, h2079, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3487_1, u2ehi3]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h1561, hlam, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        rcases p3487_3 (m.d 0 1) (by simp) with h3493 | h3493
                        · linarith only [h0, h3493, hlam]
                        · rcases p3487_3 (m.d 0 2) (by simp) with h3495 | h3495
                          · rcases p3487_3 (m.d 0 3) (by simp) with h3496 | h3496
                            · linarith only [h2078, h3496, hlam]
                            · linarith only [h1265, h3496, hlam]
                          · linarith only [h0, h3495, hlam]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        rcases p3487_3 (m.d 0 1) (by simp) with h3501 | h3501
                        · linarith only [h0, h3501, hlam]
                        · rcases p3487_3 (m.d 0 2) (by simp) with h3503 | h3503
                          · rcases p3487_3 (m.d 0 3) (by simp) with h3504 | h3504
                            · linarith only [h2078, h3504, hlam]
                            · rcases p3487_3 (m.d 0 4) (by simp) with h3506 | h3506
                              · linarith only [h2079, h3506, hlam]
                              · rcases p3487_3 (m.d 0 5) (by simp) with h3508 | h3508
                                · linarith only [h2080, h3508, hlam]
                                · linarith only [h2082, h3508, hlam]
                          · linarith only [h2078, h3503, hlam]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        rcases p3487_3 (m.d 0 1) (by simp) with h3512 | h3512
                        · linarith only [h0, h3512, hlam]
                        · rcases p3487_3 (m.d 0 2) (by simp) with h3514 | h3514
                          · rcases p3487_3 (m.d 0 3) (by simp) with h3515 | h3515
                            · linarith only [h2078, h3515, hlam]
                            · linarith only [h2081, h3515, hlam]
                          · linarith only [h2079, h3514, hlam]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        rcases p3487_3 (m.d 0 1) (by simp) with h3519 | h3519
                        · linarith only [h0, h3519, hlam]
                        · rcases p3487_3 (m.d 0 2) (by simp) with h3521 | h3521
                          · rcases p3487_3 (m.d 0 3) (by simp) with h3522 | h3522
                            · linarith only [h2078, h3522, hlam]
                            · rcases p3487_3 (m.d 0 4) (by simp) with h3524 | h3524
                              · linarith only [h2079, h3524, hlam]
                              · rcases p3487_3 (m.d 0 5) (by simp) with h3526 | h3526
                                · linarith only [h2080, h3526, hlam]
                                · rcases h3bigk with h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c | h3528c
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h1265, hlam, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h2082, h3385, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h0, h2082, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3487_1, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h2082, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h1265, hc01, hc13, hlam, hphi, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3382, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3528_1, u2ehi2]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    rcases p3528_3 (m.d 0 3) (by simp) with h3537 | h3537
                                    · linarith only [h1265, h3537, hlam]
                                    · linarith only [h2081, h3537, hlam]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h2079, h2081, h2082, h3382, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3528_1, u2ehi3]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h2078, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3382, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3481, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h2081, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3384, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3480, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3485, hlam, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h2079, h2081, h3385, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3528_1, u2ehi3]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3385, hlam, p3528_0]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3382, h3385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [h3382, h3385, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3528_1]
                                  · have p3528_0 := h3528c.1
                                    have p3528_1 := h3528c.2.1
                                    have p3528_2 := h3528c.2.2.1
                                    have p3528_3 := h3528c.2.2.2
                                    linarith only [hlam, p3528_0]
                          · linarith only [h2080, h3521, hlam]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2082, h3382, h3385, hc01, hc12, hlam, hphi, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2078, hlam, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2079, h2082, h3382, h3385, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3487_1, u2ehi3]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2082, hlam, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2081, h2082, h3382, h3385, hc01, hc12, hlam, hphi, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2079, hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2081, hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h3380, hlam, p3487_0]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2082, h3382, h3385, hc01, hc12, hlam, hphi, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2080, hlam, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h1265, h2082, h3382, h3385, hc01, hc12, hlam, hphi, p3487_1]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [h2079, h2082, h3382, h3385, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3487_1, u2ehi3]
                      · have p3487_0 := h3487c.1
                        have p3487_1 := h3487c.2.1
                        have p3487_2 := h3487c.2.2.1
                        have p3487_3 := h3487c.2.2.2
                        linarith only [hlam, p3487_0]
              · linarith only [h2081, h2082, h3382, h3385, h3480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3573 | h3573
            · linarith only [h2080, h3380, h3384, h3385, h3573, hc35, hlam, hphi, ht23, u2ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3575 | h3575
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3576 | h3576
                · linarith only [h1265, h3385, h3576, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3578 | h3578
                  · linarith only [h2079, h3380, h3578, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3580 | h3580
                    · linarith only [h2078, h2079, h3380, h3575, h3580, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases h0bigk with h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h0, hlam, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h1265, hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h0, h2079, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3582_1, u2ehi3]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h1561, hlam, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        rcases p3582_3 (m.d 0 1) (by simp) with h3588 | h3588
                        · linarith only [h0, h3588, hlam]
                        · rcases p3582_3 (m.d 0 2) (by simp) with h3590 | h3590
                          · rcases p3582_3 (m.d 0 3) (by simp) with h3591 | h3591
                            · linarith only [h2078, h3591, hlam]
                            · linarith only [h1265, h3591, hlam]
                          · linarith only [h0, h3590, hlam]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        rcases p3582_3 (m.d 0 1) (by simp) with h3596 | h3596
                        · linarith only [h0, h3596, hlam]
                        · rcases p3582_3 (m.d 0 2) (by simp) with h3598 | h3598
                          · rcases p3582_3 (m.d 0 3) (by simp) with h3599 | h3599
                            · linarith only [h2078, h3599, hlam]
                            · rcases p3582_3 (m.d 0 4) (by simp) with h3601 | h3601
                              · linarith only [h2079, h3601, hlam]
                              · rcases p3582_3 (m.d 0 5) (by simp) with h3603 | h3603
                                · linarith only [h2080, h3603, hlam]
                                · linarith only [h2082, h3603, hlam]
                          · linarith only [h2078, h3598, hlam]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        rcases p3582_3 (m.d 0 1) (by simp) with h3607 | h3607
                        · linarith only [h0, h3607, hlam]
                        · rcases p3582_3 (m.d 0 2) (by simp) with h3609 | h3609
                          · rcases p3582_3 (m.d 0 3) (by simp) with h3610 | h3610
                            · linarith only [h2078, h3610, hlam]
                            · linarith only [h2081, h3610, hlam]
                          · linarith only [h2079, h3609, hlam]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        rcases p3582_3 (m.d 0 1) (by simp) with h3614 | h3614
                        · linarith only [h0, h3614, hlam]
                        · rcases p3582_3 (m.d 0 2) (by simp) with h3616 | h3616
                          · rcases p3582_3 (m.d 0 3) (by simp) with h3617 | h3617
                            · linarith only [h2078, h3617, hlam]
                            · rcases p3582_3 (m.d 0 4) (by simp) with h3619 | h3619
                              · linarith only [h2079, h3619, hlam]
                              · rcases p3582_3 (m.d 0 5) (by simp) with h3621 | h3621
                                · linarith only [h2080, h3621, hlam]
                                · rcases h3bigk with h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h1265, hlam, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h0, h2082, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3582_1, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h0, h2082, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3582_1, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h2082, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3385, h3580, hc03, hc45, hlam, hphi, ht34, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3385, h3580, hc45, hlam, hphi, ht23, ht34, p3623_1, u2ehi2]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3385, h3580, hc34, hc45, hlam, hphi, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3385, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h2078, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3382, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3576, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h2081, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3384, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3575, hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [hlam, p3623_0]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3580, hlam, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3580, hc03, hc45, hlam, hphi, ht34, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3580, hc13, hc45, hlam, hphi, ht34, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3575, h3580, hc45, hlam, hphi, ht23, ht34, p3623_1, u2ehi3]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [h3580, hc34, hc45, hlam, hphi, p3623_1]
                                  · have p3623_0 := h3623c.1
                                    have p3623_1 := h3623c.2.1
                                    have p3623_2 := h3623c.2.2.1
                                    have p3623_3 := h3623c.2.2.2
                                    linarith only [hlam, p3623_0]
                          · linarith only [h2080, h3616, hlam]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2082, h3580, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2078, hlam, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2079, h2082, h3580, hc45, hlam, hphi, ht23, ht34, p3582_1, u2ehi3]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2082, hlam, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h1265, h2081, h3385, h3580, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2079, hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2081, hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h3380, hlam, p3582_0]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        rcases p3582_3 (m.d 0 1) (by simp) with h3660 | h3660
                        · linarith only [h1561, h3660, hlam]
                        · rcases p3582_3 (m.d 0 2) (by simp) with h3662 | h3662
                          · rcases p3582_3 (m.d 0 3) (by simp) with h3663 | h3663
                            · linarith only [h2082, h3663, hlam]
                            · linarith only [h1265, h3663, hlam]
                          · linarith only [h0, h3662, hlam]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h2080, hlam, p3582_1]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h1561, h2078, h3385, h3575, h3580, hc45, hlam, hphi, ht23, ht34, p3582_1, u2ehi3]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [h1561, h2079, h3385, h3580, hc45, hlam, hphi, ht23, ht34, p3582_1, u2ehi3]
                      · have p3582_0 := h3582c.1
                        have p3582_1 := h3582c.2.1
                        have p3582_2 := h3582c.2.2.1
                        have p3582_3 := h3582c.2.2.2
                        linarith only [hlam, p3582_0]
              · linarith only [h1265, h2081, h3385, h3575, hc23, hc35, hlam, hphi]
        · linarith only [h1265, h2081, h3384, hlam]
      · linarith only [h0, h2078, h3383, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h2078, h3382, hlam]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 3 5 (by decide) (by decide) with h2082 | h2082
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082

end R2N4
