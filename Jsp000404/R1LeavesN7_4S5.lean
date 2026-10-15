import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8294000 in
set_option maxHeartbeats 8294000 in
theorem r1l7_11_23_L_I_H_I_s7_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2917 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h2918 | h2918
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2919 | h2919
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2920 | h2920
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2921 | h2921
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2922 | h2922
          · linarith only [h2, h2922, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2924 | h2924
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2925 | h2925
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2926 | h2926
                · linarith only [h2926, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2928 | h2928
                  · linarith only [h2917, h2924, h2928, h8, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h1bigk with h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2917, h2925, hc01, hc35, hlam, hphi, ht0b, ht5b, p2930_1]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2933 | h2933
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2934 | h2934
                        · linarith only [h0, h2934, hlam]
                        · linarith only [h2917, h2934, hlam]
                      · linarith only [h2933, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2938 | h2938
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2939 | h2939
                        · linarith only [h0, h2939, hlam]
                        · linarith only [h2918, h2939, hlam]
                      · linarith only [h2938, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2943 | h2943
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2944 | h2944
                        · linarith only [h0, h2944, hlam]
                        · linarith only [h2919, h2944, hlam]
                      · linarith only [h2943, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h0, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h0, h2917, h2925, h2928, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2930_1]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2951 | h2951
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2952 | h2952
                        · rcases p2930_3 (m.d 1 3) (by simp) with h2953 | h2953
                          · linarith only [h2917, h2953, hlam]
                          · linarith only [h2920, h2953, hlam]
                        · linarith only [h2918, h2952, hlam]
                      · linarith only [h2, h2951, hlam]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2958 | h2958
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2959 | h2959
                        · rcases p2930_3 (m.d 1 3) (by simp) with h2960 | h2960
                          · linarith only [h2917, h2960, hlam]
                          · linarith only [h2921, h2960, hlam]
                        · linarith only [h2919, h2959, hlam]
                      · linarith only [h2958, h3, hlam]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h1, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2917, hlam, p2930_1]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2968 | h2968
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2969 | h2969
                        · rcases p2930_3 (m.d 1 3) (by simp) with h2970 | h2970
                          · rcases p2930_3 (m.d 1 4) (by simp) with h2971 | h2971
                            · linarith only [h2920, h2971, hlam]
                            · rcases p2930_3 (m.d 1 5) (by simp) with h2973 | h2973
                              · linarith only [h2921, h2973, hlam]
                              · linarith only [h2922, h2973, hlam]
                          · linarith only [h2920, h2970, hlam]
                        · linarith only [h2918, h2969, hlam]
                      · linarith only [h2, h2968, hlam]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h2979 | h2979
                      · rcases p2930_3 (m.d 1 2) (by simp) with h2980 | h2980
                        · rcases p2930_3 (m.d 1 3) (by simp) with h2981 | h2981
                          · rcases p2930_3 (m.d 1 4) (by simp) with h2982 | h2982
                            · linarith only [h2920, h2982, hlam]
                            · rcases p2930_3 (m.d 1 5) (by simp) with h2984 | h2984
                              · linarith only [h2921, h2984, hlam]
                              · rcases h3bigk with h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c | h2986c
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2918, h2922, h2924, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2930_1, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2925, h2928, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  rcases p2986_3 (m.d 0 3) (by simp) with h2990 | h2990
                                  · rcases p2986_3 (m.d 1 3) (by simp) with h2991 | h2991
                                    · linarith only [h1, h2991, hlam]
                                    · linarith only [h2920, h2991, hlam]
                                  · linarith only [h2990, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  rcases p2986_3 (m.d 0 3) (by simp) with h2995 | h2995
                                  · rcases p2986_3 (m.d 1 3) (by simp) with h2996 | h2996
                                    · linarith only [h1, h2996, hlam]
                                    · linarith only [h2921, h2996, hlam]
                                  · linarith only [h2995, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h1, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2925, h2928, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2917, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2917, h2928, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h4, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2917, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h2917, h2928, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h6, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2920, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2924, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2928, hlam, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h7, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2921, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h2925, hlam, p2986_0]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2986_1]
                                · have p2986_0 := h2986c.1
                                  have p2986_1 := h2986c.2.1
                                  have p2986_2 := h2986c.2.2.1
                                  have p2986_3 := h2986c.2.2.2
                                  linarith only [hlam, p2986_0]
                          · linarith only [h2921, h2981, hlam]
                        · linarith only [h2919, h2980, hlam]
                      · linarith only [h2979, h3, hlam]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2918, hlam, p2930_1]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2920, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2922, hlam, p2930_1]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h3, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2919, hlam, p2930_1]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [h2921, hlam, p2930_0]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      rcases p2930_3 (m.d 0 1) (by simp) with h3031 | h3031
                      · rcases p2930_3 (m.d 1 2) (by simp) with h3032 | h3032
                        · rcases p2930_3 (m.d 1 3) (by simp) with h3033 | h3033
                          · rcases p2930_3 (m.d 1 4) (by simp) with h3034 | h3034
                            · linarith only [h2922, h3034, hlam]
                            · rcases p2930_3 (m.d 1 5) (by simp) with h3036 | h3036
                              · rcases h3bigk with h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h2917, h2925, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h2925, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  rcases p3037_3 (m.d 0 3) (by simp) with h3041 | h3041
                                  · rcases p3037_3 (m.d 1 3) (by simp) with h3042 | h3042
                                    · linarith only [h1, h3042, hlam]
                                    · linarith only [h2920, h3042, hlam]
                                  · linarith only [h3041, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  rcases p3037_3 (m.d 0 3) (by simp) with h3046 | h3046
                                  · rcases p3037_3 (m.d 1 3) (by simp) with h3047 | h3047
                                    · linarith only [h1, h3047, hlam]
                                    · linarith only [h2921, h3047, hlam]
                                  · linarith only [h3046, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h1, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2925, h2928, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h2917, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h2917, h2928, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h4, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2917, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h2917, h2928, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h6, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2920, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2924, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2928, hlam, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h7, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2921, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h2925, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                              · linarith only [h2922, h3036, hlam]
                          · linarith only [h2920, h3033, hlam]
                        · linarith only [h2918, h3032, hlam]
                      · linarith only [h2, h3031, hlam]
                    · have p2930_0 := h2930c.1
                      have p2930_1 := h2930c.2.1
                      have p2930_2 := h2930c.2.2.1
                      have p2930_3 := h2930c.2.2.2
                      linarith only [hlam, p2930_0]
              · linarith only [h0, h2917, h2921, h2924, h2925, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3077 | h3077
              · linarith only [h0, h2917, h2920, h2924, h3077, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3079 | h3079
                · linarith only [h0, h2, h2920, h2924, h3079, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3081 | h3081
                  · linarith only [h2, h2920, h3081, h8, hlam]
                  · rcases h1bigk with h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c | h3083c
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2917, h2921, h2924, h3081, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2921, h2924, h3081, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      rcases p3083_3 (m.d 0 1) (by simp) with h3087 | h3087
                      · rcases p3083_3 (m.d 1 2) (by simp) with h3088 | h3088
                        · linarith only [h0, h3088, hlam]
                        · linarith only [h2918, h3088, hlam]
                      · linarith only [h3087, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      rcases p3083_3 (m.d 0 1) (by simp) with h3092 | h3092
                      · rcases p3083_3 (m.d 1 2) (by simp) with h3093 | h3093
                        · linarith only [h0, h3093, hlam]
                        · linarith only [h2919, h3093, hlam]
                      · linarith only [h3092, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h0, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2921, h2924, h3081, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h0, h2920, h2924, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h0, h2921, h2924, h3081, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h1, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2917, hlam, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h1, h2920, h2924, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h0, h2917, h2921, h2924, h3081, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2918, hlam, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2920, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2922, hlam, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h3, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2919, hlam, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2921, hlam, p3083_0]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [h2920, h2924, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3083_1]
                    · have p3083_0 := h3083c.1
                      have p3083_1 := h3083c.2.1
                      have p3083_2 := h3083c.2.2.1
                      have p3083_3 := h3083c.2.2.2
                      linarith only [hlam, p3083_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3117 | h3117
          · linarith only [h2920, h2921, h3117, h7, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3119 | h3119
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3120 | h3120
              · linarith only [h2917, h2921, h3120, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3122 | h3122
                · linarith only [h2918, h2920, h2921, h3122, h7, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3124 | h3124
                  · linarith only [h2917, h2921, h3119, h3124, h7, h8, hlam]
                  · rcases h1bigk with h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2917, h3119, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      rcases p3126_3 (m.d 0 1) (by simp) with h3129 | h3129
                      · rcases p3126_3 (m.d 1 2) (by simp) with h3130 | h3130
                        · linarith only [h0, h3130, hlam]
                        · linarith only [h2917, h3130, hlam]
                      · linarith only [h3129, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      rcases p3126_3 (m.d 0 1) (by simp) with h3134 | h3134
                      · rcases p3126_3 (m.d 1 2) (by simp) with h3135 | h3135
                        · linarith only [h0, h3135, hlam]
                        · linarith only [h2918, h3135, hlam]
                      · linarith only [h3134, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      rcases p3126_3 (m.d 0 1) (by simp) with h3139 | h3139
                      · rcases p3126_3 (m.d 1 2) (by simp) with h3140 | h3140
                        · linarith only [h0, h3140, hlam]
                        · linarith only [h2919, h3140, hlam]
                      · linarith only [h3139, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h0, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h0, h2917, h3119, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      rcases p3126_3 (m.d 0 1) (by simp) with h3147 | h3147
                      · rcases p3126_3 (m.d 1 2) (by simp) with h3148 | h3148
                        · rcases p3126_3 (m.d 1 3) (by simp) with h3149 | h3149
                          · linarith only [h2917, h3149, hlam]
                          · linarith only [h2920, h3149, hlam]
                        · linarith only [h2918, h3148, hlam]
                      · linarith only [h2, h3147, hlam]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h0, h2919, h3119, h3120, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h1, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2917, hlam, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2918, h2921, h7, h8, hc24, hc45, hlam, hphi, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2921, hlam, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2918, hlam, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2920, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h3117, hlam, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h3, hlam, p3126_0]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2919, hlam, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [h2917, h3, h3119, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3126_1]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      rcases p3126_3 (m.d 0 1) (by simp) with h3168 | h3168
                      · rcases p3126_3 (m.d 1 2) (by simp) with h3169 | h3169
                        · rcases p3126_3 (m.d 1 3) (by simp) with h3170 | h3170
                          · linarith only [h2921, h3170, hlam]
                          · linarith only [h2920, h3170, hlam]
                        · linarith only [h2918, h3169, hlam]
                      · linarith only [h2, h3168, hlam]
                    · have p3126_0 := h3126c.1
                      have p3126_1 := h3126c.2.1
                      have p3126_2 := h3126c.2.2.1
                      have p3126_3 := h3126c.2.2.2
                      linarith only [hlam, p3126_0]
            · linarith only [h0, h2920, h2921, h3119, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3177 | h3177
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3178 | h3178
          · linarith only [h2920, h3177, h3178, h6, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2920, h3177, h3178, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3181 | h3181
          · linarith only [h2, h2920, h3181, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3183 | h3183
            · linarith only [h2917, h2920, h3183, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3185 | h3185
              · linarith only [h2917, h3177, h3185, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3187 | h3187
                · linarith only [h2, h2917, h2918, h2920, h3187, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3189 | h3189
                  · linarith only [h3189, h6, h8, hlam]
                  · rcases h1bigk with h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3193 | h3193
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3194 | h3194
                        · linarith only [h3194, hlam, p3191_0]
                        · rcases p3191_3 (m.d 1 3) (by simp) with h3196 | h3196
                          · linarith only [h1, h3196, hlam]
                          · rcases p3191_3 (m.d 1 4) (by simp) with h3198 | h3198
                            · linarith only [h2, h3198, hlam]
                            · rcases p3191_3 (m.d 1 5) (by simp) with h3200 | h3200
                              · linarith only [h3, h3200, hlam]
                              · rcases h3bigk with h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  rcases p3202_3 (m.d 0 3) (by simp) with h3204 | h3204
                                  · rcases p3202_3 (m.d 1 3) (by simp) with h3205 | h3205
                                    · linarith only [h1, h3205, hlam]
                                    · rcases p3202_3 (m.d 2 3) (by simp) with h3207 | h3207
                                      · linarith only [h3207, h4, hlam]
                                      · rcases p3202_3 (m.d 3 4) (by simp) with h3209 | h3209
                                        · linarith only [h3209, h6, hlam]
                                        · linarith only [h2920, h3209, hlam]
                                  · linarith only [h1, h3204, hlam]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  rcases p3202_3 (m.d 0 3) (by simp) with h3213 | h3213
                                  · rcases p3202_3 (m.d 1 3) (by simp) with h3214 | h3214
                                    · linarith only [h1, h3214, hlam]
                                    · linarith only [h2917, h3214, hlam]
                                  · linarith only [h3213, h4, hlam]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h0, h2917, h2920, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h0, h2917, h3177, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h1, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h2920, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h2920, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h3177, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h4, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h2917, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h3183, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h3185, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h6, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [hc13, hc34, hlam, hphi, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h3189, hlam, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h7, hlam, p3202_0]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h2917, hc23, hc35, hlam, hphi, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3202_1]
                                · have p3202_0 := h3202c.1
                                  have p3202_1 := h3202c.2.1
                                  have p3202_2 := h3202c.2.2.1
                                  have p3202_3 := h3202c.2.2.2
                                  linarith only [hlam, p3202_0]
                      · linarith only [h3193, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3241 | h3241
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3242 | h3242
                        · linarith only [h0, h3242, hlam]
                        · linarith only [h2917, h3242, hlam]
                      · linarith only [h3241, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3246 | h3246
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3247 | h3247
                        · linarith only [h0, h3247, hlam]
                        · linarith only [h2918, h3247, hlam]
                      · linarith only [h3246, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3251 | h3251
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3252 | h3252
                        · linarith only [h0, h3252, hlam]
                        · linarith only [h2919, h3252, hlam]
                      · linarith only [h3251, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h0, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3258 | h3258
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3259 | h3259
                        · rcases p3191_3 (m.d 1 3) (by simp) with h3260 | h3260
                          · linarith only [h2917, h3260, hlam]
                          · rcases p3191_3 (m.d 1 4) (by simp) with h3262 | h3262
                            · linarith only [h2918, h3262, hlam]
                            · linarith only [h2920, h3262, hlam]
                        · linarith only [h2917, h3259, hlam]
                      · linarith only [h1, h3258, hlam]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3267 | h3267
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3268 | h3268
                        · rcases p3191_3 (m.d 1 3) (by simp) with h3269 | h3269
                          · linarith only [h2917, h3269, hlam]
                          · rcases p3191_3 (m.d 1 4) (by simp) with h3271 | h3271
                            · linarith only [h2918, h3271, hlam]
                            · rcases p3191_3 (m.d 1 5) (by simp) with h3273 | h3273
                              · linarith only [h2919, h3273, hlam]
                              · linarith only [h3181, h3273, hlam]
                        · linarith only [h2918, h3268, hlam]
                      · linarith only [h2, h3267, hlam]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3278 | h3278
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3279 | h3279
                        · rcases p3191_3 (m.d 1 3) (by simp) with h3280 | h3280
                          · linarith only [h2917, h3280, hlam]
                          · rcases p3191_3 (m.d 1 4) (by simp) with h3282 | h3282
                            · linarith only [h2918, h3282, hlam]
                            · rcases p3191_3 (m.d 1 5) (by simp) with h3284 | h3284
                              · linarith only [h2919, h3284, hlam]
                              · rcases h3bigk with h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  rcases p3286_3 (m.d 0 3) (by simp) with h3288 | h3288
                                  · rcases p3286_3 (m.d 1 3) (by simp) with h3289 | h3289
                                    · linarith only [h1, h3289, hlam]
                                    · rcases p3286_3 (m.d 2 3) (by simp) with h3291 | h3291
                                      · linarith only [h3291, h4, hlam]
                                      · rcases p3286_3 (m.d 3 4) (by simp) with h3293 | h3293
                                        · linarith only [h3293, h6, hlam]
                                        · linarith only [h2920, h3293, hlam]
                                  · linarith only [h1, h3288, hlam]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  rcases p3286_3 (m.d 0 3) (by simp) with h3297 | h3297
                                  · rcases p3286_3 (m.d 1 3) (by simp) with h3298 | h3298
                                    · linarith only [h1, h3298, hlam]
                                    · linarith only [h2917, h3298, hlam]
                                  · linarith only [h3297, h4, hlam]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h0, h2917, h2920, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h0, h2917, h3177, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h1, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h2920, h3181, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3191_1, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h2920, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h3177, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h4, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h2917, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h3183, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h3185, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h6, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hc13, hc34, hlam, hphi, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h3189, hlam, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h7, hlam, p3286_0]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hc13, hc35, hlam, hphi, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3286_1]
                                · have p3286_0 := h3286c.1
                                  have p3286_1 := h3286c.2.1
                                  have p3286_2 := h3286c.2.2.1
                                  have p3286_3 := h3286c.2.2.2
                                  linarith only [hlam, p3286_0]
                        · linarith only [h2919, h3279, hlam]
                      · linarith only [h3, h3278, hlam]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h1, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h2917, hlam, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h2920, hlam, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h3177, hlam, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h2, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h2918, hlam, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h2, h8, hc13, hc45, hlam, hphi, ht34, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h3181, hlam, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h3, hlam, p3191_0]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [h2919, hlam, p3191_1]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3338 | h3338
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3339 | h3339
                        · rcases p3191_3 (m.d 1 3) (by simp) with h3340 | h3340
                          · linarith only [h3177, h3340, hlam]
                          · rcases p3191_3 (m.d 1 4) (by simp) with h3342 | h3342
                            · linarith only [h3181, h3342, hlam]
                            · linarith only [h2920, h3342, hlam]
                        · linarith only [h2917, h3339, hlam]
                      · linarith only [h1, h3338, hlam]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      rcases p3191_3 (m.d 0 1) (by simp) with h3347 | h3347
                      · rcases p3191_3 (m.d 1 2) (by simp) with h3348 | h3348
                        · rcases p3191_3 (m.d 1 3) (by simp) with h3349 | h3349
                          · linarith only [h3177, h3349, hlam]
                          · rcases p3191_3 (m.d 1 4) (by simp) with h3351 | h3351
                            · linarith only [h3181, h3351, hlam]
                            · rcases p3191_3 (m.d 1 5) (by simp) with h3353 | h3353
                              · rcases h3bigk with h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  rcases p3354_3 (m.d 0 3) (by simp) with h3356 | h3356
                                  · rcases p3354_3 (m.d 1 3) (by simp) with h3357 | h3357
                                    · linarith only [h1, h3357, hlam]
                                    · rcases p3354_3 (m.d 2 3) (by simp) with h3359 | h3359
                                      · linarith only [h3359, h4, hlam]
                                      · rcases p3354_3 (m.d 3 4) (by simp) with h3361 | h3361
                                        · linarith only [h3361, h6, hlam]
                                        · linarith only [h2920, h3361, hlam]
                                  · linarith only [h1, h3356, hlam]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  rcases p3354_3 (m.d 0 3) (by simp) with h3365 | h3365
                                  · rcases p3354_3 (m.d 1 3) (by simp) with h3366 | h3366
                                    · linarith only [h1, h3366, hlam]
                                    · linarith only [h2917, h3366, hlam]
                                  · linarith only [h3365, h4, hlam]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h0, h2917, h2920, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h0, h3177, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3191_1, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h1, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h2920, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h3177, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h4, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h2917, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h3183, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h3185, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h6, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [hc13, hc34, hlam, hphi, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h3189, hlam, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h7, hlam, p3354_0]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h2917, hc23, hc35, hlam, hphi, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3354_1]
                                · have p3354_0 := h3354c.1
                                  have p3354_1 := h3354c.2.1
                                  have p3354_2 := h3354c.2.2.1
                                  have p3354_3 := h3354c.2.2.2
                                  linarith only [hlam, p3354_0]
                              · linarith only [h3181, h3353, hlam]
                        · linarith only [h2918, h3348, hlam]
                      · linarith only [h2, h3347, hlam]
                    · have p3191_0 := h3191c.1
                      have p3191_1 := h3191c.2.1
                      have p3191_2 := h3191c.2.2.1
                      have p3191_3 := h3191c.2.2.2
                      linarith only [hlam, p3191_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3396 | h3396
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3397 | h3397
        · linarith only [h2917, h2919, h3397, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3399 | h3399
          · linarith only [h2, h3399, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3401 | h3401
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3402 | h3402
              · linarith only [h2917, h2919, h3397, h3402, hlam]
              · linarith only [h2917, h2919, h3401, h3402, h7, h8, hc34, hc45, hlam, hphi]
            · linarith only [h0, h3396, h3397, h3401, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3406 | h3406
        · linarith only [h2917, h2919, h3396, h3406, h6, h8, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3408 | h3408
          · linarith only [h2, h3408, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3410 | h3410
            · linarith only [h2917, h3396, h3410, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3412 | h3412
              · linarith only [h2918, h2919, h3406, h3410, h3412, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3414 | h3414
                · linarith only [h2918, h2919, h3412, h3414, h7, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3416 | h3416
                  · linarith only [h2918, h2919, h3410, h3412, h3416, h7, h8, hc23, hc34, hlam, hphi]
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
                      rcases p3418_3 (m.d 0 1) (by simp) with h3420 | h3420
                      · rcases p3418_3 (m.d 1 2) (by simp) with h3421 | h3421
                        · linarith only [h3421, hlam, p3418_0]
                        · rcases p3418_3 (m.d 1 3) (by simp) with h3423 | h3423
                          · linarith only [h1, h3423, hlam]
                          · rcases p3418_3 (m.d 1 4) (by simp) with h3425 | h3425
                            · linarith only [h2, h3425, hlam]
                            · rcases p3418_3 (m.d 1 5) (by simp) with h3427 | h3427
                              · linarith only [h3, h3427, hlam]
                              · linarith only [h2919, h3427, hlam]
                      · linarith only [h3420, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      rcases p3418_3 (m.d 0 1) (by simp) with h3431 | h3431
                      · rcases p3418_3 (m.d 1 2) (by simp) with h3432 | h3432
                        · linarith only [h0, h3432, hlam]
                        · linarith only [h2917, h3432, hlam]
                      · linarith only [h3431, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      rcases p3418_3 (m.d 0 1) (by simp) with h3436 | h3436
                      · rcases p3418_3 (m.d 1 2) (by simp) with h3437 | h3437
                        · linarith only [h0, h3437, hlam]
                        · linarith only [h2918, h3437, hlam]
                      · linarith only [h3436, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      rcases p3418_3 (m.d 0 1) (by simp) with h3441 | h3441
                      · rcases p3418_3 (m.d 1 2) (by simp) with h3442 | h3442
                        · linarith only [h0, h3442, hlam]
                        · rcases p3418_3 (m.d 1 3) (by simp) with h3444 | h3444
                          · linarith only [h1, h3444, hlam]
                          · rcases p3418_3 (m.d 1 4) (by simp) with h3446 | h3446
                            · linarith only [h2, h3446, hlam]
                            · rcases p3418_3 (m.d 1 5) (by simp) with h3448 | h3448
                              · linarith only [h3448, hlam, p3418_0]
                              · rcases h3bigk with h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  rcases p3450_3 (m.d 0 3) (by simp) with h3452 | h3452
                                  · rcases p3450_3 (m.d 1 3) (by simp) with h3453 | h3453
                                    · linarith only [h1, h3453, hlam]
                                    · rcases p3450_3 (m.d 2 3) (by simp) with h3455 | h3455
                                      · linarith only [h3455, h4, hlam]
                                      · rcases p3450_3 (m.d 3 4) (by simp) with h3457 | h3457
                                        · linarith only [h3457, h6, hlam]
                                        · linarith only [h3396, h3457, hlam]
                                  · linarith only [h1, h3452, hlam]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  rcases p3450_3 (m.d 0 3) (by simp) with h3461 | h3461
                                  · rcases p3450_3 (m.d 1 3) (by simp) with h3462 | h3462
                                    · linarith only [h1, h3462, hlam]
                                    · linarith only [h2917, h3462, hlam]
                                  · linarith only [h3461, h4, hlam]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h0, h3396, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h0, h2918, h2919, h3410, h3412, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h1, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h3396, hc23, hc34, hlam, hphi, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h3396, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h3406, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h4, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h2917, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h3410, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h3412, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h6, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [hc13, hc34, hlam, hphi, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h3416, hlam, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h7, hlam, p3450_0]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h2917, hc23, hc35, hlam, hphi, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                                · have p3450_0 := h3450c.1
                                  have p3450_1 := h3450c.2.1
                                  have p3450_2 := h3450c.2.2.1
                                  have p3450_3 := h3450c.2.2.2
                                  linarith only [hlam, p3450_0]
                      · linarith only [h3441, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h0, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h0, h2917, h2919, h3412, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h0, h2918, h2919, h3410, h3412, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h2919, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h1, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h2917, hlam, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h3396, hlam, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h3406, hlam, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h2, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h2918, hlam, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h2, h2917, h8, hc23, hc45, hlam, hphi, ht34, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h3408, hlam, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h3, hlam, p3418_0]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [h2917, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3418_1]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      rcases p3418_3 (m.d 0 1) (by simp) with h3506 | h3506
                      · rcases p3418_3 (m.d 1 2) (by simp) with h3507 | h3507
                        · linarith only [h2919, h3507, hlam]
                        · linarith only [h2917, h3507, hlam]
                      · linarith only [h1, h3506, hlam]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      rcases p3418_3 (m.d 0 1) (by simp) with h3511 | h3511
                      · rcases p3418_3 (m.d 1 2) (by simp) with h3512 | h3512
                        · linarith only [h2919, h3512, hlam]
                        · linarith only [h2918, h3512, hlam]
                      · linarith only [h2, h3511, hlam]
                    · have p3418_0 := h3418c.1
                      have p3418_1 := h3418c.2.1
                      have p3418_2 := h3418c.2.2.1
                      have p3418_3 := h3418c.2.2.2
                      linarith only [hlam, p3418_0]
  · linarith only [h2917, h2918, h5, h8, hc23, hc45, hlam, hphi, ht34]

end R2N4
