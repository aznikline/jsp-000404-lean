import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h905 | h905
  · rcases m.htr 0 2 5 (by decide) (by decide) with h906 | h906
    · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
      · rcases m.htr 0 3 5 (by decide) (by decide) with h908 | h908
        · rcases m.htr 0 4 5 (by decide) (by decide) with h909 | h909
          · rcases m.htr 1 2 3 (by decide) (by decide) with h910 | h910
            · linarith only [h4, h905, h910, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
              · rcases m.htr 1 2 5 (by decide) (by decide) with h913 | h913
                · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h915 | h915
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h916 | h916
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h917 | h917
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h918 | h918
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h919 | h919
                            · linarith only [h1, h910, h912, h919, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h4, h905, h909, h917, h919, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h4, h908, h918, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h4, h907, h917, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h4, h905, h909, h916, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h4, h908, h910, h912, h915, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h4, h907, h910, h912, h914, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h906, h912, h913, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h905, h912, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h929 | h929
            · linarith only [h4, h929, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h931 | h931
              · rcases m.htr 1 2 5 (by decide) (by decide) with h932 | h932
                · rcases m.htr 1 3 4 (by decide) (by decide) with h933 | h933
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h934 | h934
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h935 | h935
                      · linarith only [h2, h909, h935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h937 | h937
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h938 | h938
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h939 | h939
                            · linarith only [h0, h909, h931, h939, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h941 | h941
                              · linarith only [h3, h4, h905, h909, h937, h941, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · rcases h0bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, h932, h937, h939, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h1, h929, h932, h937, h939, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  rcases p943_3 (m.d 0 1) (by simp) with h947 | h947
                                  · rcases p943_3 (m.d 0 2) (by simp) with h948 | h948
                                    · linarith only [h0, h948, hlam]
                                    · linarith only [h905, h948, hlam]
                                  · linarith only [h2, h947, hlam]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  rcases p943_3 (m.d 0 1) (by simp) with h952 | h952
                                  · rcases p943_3 (m.d 0 2) (by simp) with h953 | h953
                                    · linarith only [h0, h953, hlam]
                                    · linarith only [h906, h953, hlam]
                                  · linarith only [h3, h952, hlam]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h4, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h4, h905, h909, h937, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h1, hlam, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, h932, h937, h939, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  rcases p943_3 (m.d 0 1) (by simp) with h965 | h965
                                  · rcases p943_3 (m.d 0 2) (by simp) with h966 | h966
                                    · linarith only [h4, h966, hlam]
                                    · linarith only [h905, h966, hlam]
                                  · linarith only [h2, h965, hlam]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  rcases p943_3 (m.d 0 1) (by simp) with h970 | h970
                                  · rcases p943_3 (m.d 0 2) (by simp) with h971 | h971
                                    · linarith only [h4, h971, hlam]
                                    · linarith only [h906, h971, hlam]
                                  · linarith only [h3, h970, hlam]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h2, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h905, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h907, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h909, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h3, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h906, hlam, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h908, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h2, h4, h906, h931, h937, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                          · linarith only [h4, h908, h938, hlam]
                        · linarith only [h4, h907, h937, hlam]
                    · linarith only [h4, h906, h908, h929, h931, h934, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h4, h907, h929, h931, h933, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h906, h931, h932, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h905, h931, hc12, hlam, hphi, u2elo2]
        · linarith only [h4, h906, h908, hlam]
      · linarith only [h4, h905, h907, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h993 | h993
      · rcases m.htr 0 3 5 (by decide) (by decide) with h994 | h994
        · rcases m.htr 0 4 5 (by decide) (by decide) with h995 | h995
          · linarith only [h905, h906, h995, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
            · linarith only [h4, h997, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1000 | h1000
                · linarith only [h0, h1000, h906, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1002 | h1002
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1003 | h1003
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1004 | h1004
                      · linarith only [h1004, h2, h995, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1006 | h1006
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1007 | h1007
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1008 | h1008
                            · linarith only [h0, h1008, h906, h995, h999, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                              · linarith only [h0, h1006, h1008, h1010, h906, h999, hlam]
                              · rcases h0bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, h1006, h999, hc34, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u0elo0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, h1006, h906, h994, h999, hc34, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u0elo0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  rcases p1012_3 (m.d 0 1) (by simp) with h1016 | h1016
                                  · rcases p1012_3 (m.d 0 2) (by simp) with h1017 | h1017
                                    · linarith only [h0, h1017, hlam]
                                    · linarith only [h1017, h905, hlam]
                                  · linarith only [h1016, h2, hlam]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, h1006, h906, h999, hc34, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u0elo0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h4, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h1006, h1007, h2, h906, h999, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1012_1, u2elo2]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h906, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h1, hlam, p1012_1]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, h1006, h999, hc34, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u0elo2]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  rcases p1012_3 (m.d 0 1) (by simp) with h1030 | h1030
                                  · rcases p1012_3 (m.d 0 2) (by simp) with h1031 | h1031
                                    · linarith only [h1031, h4, hlam]
                                    · linarith only [h1031, h905, hlam]
                                  · linarith only [h1030, h2, hlam]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, h1006, h4, h906, h999, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1012_1, u2elo2]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h2, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h905, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h993, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h995, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h3, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h0, h1006, h999, hc34, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u0elo4]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [h994, hlam, p1012_0]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  rcases p1012_3 (m.d 0 1) (by simp) with h1044 | h1044
                                  · rcases p1012_3 (m.d 0 2) (by simp) with h1045 | h1045
                                    · linarith only [h1045, h906, hlam]
                                    · linarith only [h1045, h905, hlam]
                                  · linarith only [h1044, h2, hlam]
                                · have p1012_0 := h1012c.1
                                  have p1012_1 := h1012c.2.1
                                  have p1012_2 := h1012c.2.2.1
                                  have p1012_3 := h1012c.2.2.2
                                  linarith only [hlam, p1012_0]
                          · linarith only [h1, h1003, h1007, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1006, h4, h993, hlam]
                    · linarith only [h1003, h4, h994, h997, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1002, h4, h993, h997, h999, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h905, h999, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1055 | h1055
          · linarith only [h1055, h4, h905, h994, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1057 | h1057
            · linarith only [h1057, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1059 | h1059
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                · linarith only [h0, h1060, h906, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1062 | h1062
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1063 | h1063
                    · linarith only [h0, h1, h1059, h1063, h4, h994, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1065 | h1065
                      · linarith only [h1055, h1065, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1067 | h1067
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1068 | h1068
                          · linarith only [h0, h1059, h1067, h1068, h4, h994, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1070 | h1070
                            · linarith only [h0, h1055, h1059, h1070, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1072 | h1072
                              · linarith only [h0, h1059, h1067, h1068, h1070, h1072, h4, hlam]
                              · linarith only [h0, h1059, h1068, h1072, h4, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h1059, h1067, h4, h906, h993, h994, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h1062, h993, h994, hc13, hc35, hlam, hphi]
              · linarith only [h1059, h4, h905, hc12, hlam, hphi, u2elo2]
      · linarith only [h4, h905, h993, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1079 | h1079
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1080 | h1080
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1081 | h1081
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1082 | h1082
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1083 | h1083
            · linarith only [h1083, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1085 | h1085
              · linarith only [h0, h1085, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1087 | h1087
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1088 | h1088
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1092 | h1092
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1093 | h1093
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1094 | h1094
                              · linarith only [h1, h1088, h1094, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1090, h1094, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h1, h1087, h1088, h1090, h1092, h1093, h905, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1081, h1091, h1092, h905, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1080, h1091, h4, hlam]
                      · linarith only [h1080, h1082, h1085, h1087, h1090, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h1081, h1088, h1089, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1080, h1083, h1087, h1088, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1079, h1087, hc12, hlam, hphi, u2elo0]
          · linarith only [h1079, h1082, h905, hlam]
        · linarith only [h1079, h1081, h4, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1106 | h1106
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1107 | h1107
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1108 | h1108
            · linarith only [h1108, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
              · linarith only [h0, h1110, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1112 | h1112
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1113 | h1113
                  · linarith only [h1, h1080, h1113, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1117 | h1117
                        · linarith only [h0, h1080, h1112, h1117, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1119 | h1119
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1120 | h1120
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1121 | h1121
                              · rcases h0bigk with h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, h1112, h1119, h1121, hc45, hlam, hphi, ht0b, ht5b, p1122_1, u0elo0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, h1112, h1119, h1121, h4, hc45, hlam, hphi, ht0b, ht5b, p1122_1, u0elo0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, h1080, h1112, h1119, h1121, h4, hc45, hlam, hphi, ht0b, ht5b, p1122_1, u0elo0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  rcases p1122_3 (m.d 0 1) (by simp) with h1127 | h1127
                                  · rcases p1122_3 (m.d 0 2) (by simp) with h1128 | h1128
                                    · linarith only [h0, h1128, hlam]
                                    · linarith only [h1079, h1128, hlam]
                                  · linarith only [h1127, h3, hlam]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h4, hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h905, hlam, p1122_1]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo2]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h1, hlam, p1122_1]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, h1080, h1112, hc25, hlam, hphi, ht0b, ht5b, p1122_1, u0elo3]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h1080, hlam, p1122_1]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  rcases p1122_3 (m.d 0 1) (by simp) with h1141 | h1141
                                  · rcases p1122_3 (m.d 0 2) (by simp) with h1142 | h1142
                                    · linarith only [h1142, h4, hlam]
                                    · linarith only [h1079, h1142, hlam]
                                  · linarith only [h1141, h3, hlam]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h2, hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, h1112, h1119, h1121, h905, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo3]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h0, h1112, h1119, h1121, h4, h905, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo3]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  rcases p1122_3 (m.d 0 1) (by simp) with h1150 | h1150
                                  · rcases p1122_3 (m.d 0 2) (by simp) with h1151 | h1151
                                    · linarith only [h1151, h905, hlam]
                                    · linarith only [h1079, h1151, hlam]
                                  · linarith only [h1150, h3, hlam]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h3, hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h1079, hlam, p1122_1]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h1106, hlam, p1122_0]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [h1107, hlam, p1122_1]
                                · have p1122_0 := h1122c.1
                                  have p1122_1 := h1122c.2.1
                                  have p1122_2 := h1122c.2.2.1
                                  have p1122_3 := h1122c.2.2.2
                                  linarith only [hlam, p1122_0]
                              · linarith only [h1080, h1107, h1121, hlam]
                            · linarith only [h1107, h1120, h905, hlam]
                          · linarith only [h1106, h1119, h4, hlam]
                      · linarith only [h1079, h1107, h1108, h1113, h1116, h4, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1080, h1106, h1108, h1112, h1115, h905, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h1079, h1112, h4, hc12, hlam, hphi, u2elo2]
          · linarith only [h1079, h1080, h1107, h4, hlam]
        · linarith only [h1079, h1106, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1169 | h1169
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1170 | h1170
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1171 | h1171
            · linarith only [h1171, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1173 | h1173
              · linarith only [h0, h1173, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1175 | h1175
                · linarith only [h0, h1079, h1175, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1177 | h1177
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1178 | h1178
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1179 | h1179
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1180 | h1180
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1181 | h1181
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1182 | h1182
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1183 | h1183
                              · linarith only [h1, h1177, h1183, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1179, h1183, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h1177, h1179, h1182, h905, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1178, h1181, h3, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1168, h1180, h4, hlam]
                      · linarith only [h1168, h1170, h1173, h1179, h4, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1169, h1171, h1178, h4, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1168, h1171, h1177, h4, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1192 | h1192
            · linarith only [h1192, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1194 | h1194
              · linarith only [h0, h1194, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1196 | h1196
                · linarith only [h0, h1079, h1196, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1200 | h1200
                      · linarith only [h1170, h1200, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1202 | h1202
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1203 | h1203
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1204 | h1204
                            · linarith only [h0, h1170, h1202, h1204, h905, hc12, hlam, hphi, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1206 | h1206
                              · linarith only [h0, h1204, h1206, h905, hc12, hc34, hlam, hphi, ht23]
                              · rcases h0bigk with h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  rcases p1208_3 (m.d 0 1) (by simp) with h1210 | h1210
                                  · rcases p1208_3 (m.d 0 2) (by simp) with h1211 | h1211
                                    · linarith only [h0, h1211, hlam]
                                    · rcases p1208_3 (m.d 0 3) (by simp) with h1213 | h1213
                                      · linarith only [h1, h1213, hlam]
                                      · linarith only [h1213, h4, hlam]
                                  · linarith only [h0, h1210, hlam]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h1, h1199, hc35, hlam, hphi, ht0b, ht5b, p1208_1, u0elo0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  rcases p1208_3 (m.d 0 1) (by simp) with h1218 | h1218
                                  · rcases p1208_3 (m.d 0 2) (by simp) with h1219 | h1219
                                    · linarith only [h0, h1219, hlam]
                                    · rcases p1208_3 (m.d 0 3) (by simp) with h1221 | h1221
                                      · linarith only [h1, h1221, hlam]
                                      · linarith only [h1168, h1221, hlam]
                                  · linarith only [h1218, h2, hlam]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  rcases p1208_3 (m.d 0 1) (by simp) with h1225 | h1225
                                  · rcases p1208_3 (m.d 0 2) (by simp) with h1226 | h1226
                                    · linarith only [h0, h1226, hlam]
                                    · rcases p1208_3 (m.d 0 3) (by simp) with h1228 | h1228
                                      · linarith only [h1, h1228, hlam]
                                      · linarith only [h1169, h1228, hlam]
                                  · linarith only [h1225, h3, hlam]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h4, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h905, hlam, p1208_1]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h1079, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h1, hlam, p1208_1]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, h4, hc12, hlam, hphi, p1208_1, u2elo2]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, h4, h905, hc12, hlam, hphi, p1208_1, u2elo2]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, h1079, h4, hc12, hlam, hphi, p1208_1, u2elo2]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h2, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, h905, hc12, hlam, hphi, p1208_1, u2elo3]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h1168, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h1170, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h3, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, h1079, hc12, hlam, hphi, p1208_1, u2elo4]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h1169, hlam, p1208_0]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [h0, h1169, h4, h905, hc12, hlam, hphi, p1208_1, u2elo2]
                                · have p1208_0 := h1208c.1
                                  have p1208_1 := h1208c.2.1
                                  have p1208_2 := h1208c.2.2.1
                                  have p1208_3 := h1208c.2.2.2
                                  linarith only [hlam, p1208_0]
                          · linarith only [h1169, h1203, h4, hlam]
                        · linarith only [h0, h1168, h1202, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1169, h1198, h1199, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1168, h1192, h1198, h4, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1256 | h1256
          · linarith only [h1168, h1169, h1256, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
            · linarith only [h0, h1258, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1260 | h1260
              · linarith only [h0, h1260, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1262 | h1262
                · linarith only [h1, h1079, h1169, h1258, h1262, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1264 | h1264
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1265 | h1265
                    · linarith only [h1, h1169, h1265, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1267 | h1267
                      · linarith only [h0, h1256, h1267, h2, h905, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1269 | h1269
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1270 | h1270
                          · linarith only [h1, h1169, h1264, h1270, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1272 | h1272
                            · linarith only [h0, h1256, h1272, h905, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                              · linarith only [h1, h1264, h1272, h1274, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · rcases h0bigk with h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  rcases p1276_3 (m.d 0 1) (by simp) with h1278 | h1278
                                  · rcases p1276_3 (m.d 0 2) (by simp) with h1279 | h1279
                                    · linarith only [h0, h1279, hlam]
                                    · rcases p1276_3 (m.d 0 3) (by simp) with h1281 | h1281
                                      · linarith only [h1, h1281, hlam]
                                      · linarith only [h1281, h4, hlam]
                                  · linarith only [h0, h1278, hlam]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1, h1264, hc34, hlam, hphi, ht0b, ht45, ht5b, p1276_1, u0elo0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  rcases p1276_3 (m.d 0 1) (by simp) with h1286 | h1286
                                  · rcases p1276_3 (m.d 0 2) (by simp) with h1287 | h1287
                                    · linarith only [h0, h1287, hlam]
                                    · rcases p1276_3 (m.d 0 3) (by simp) with h1289 | h1289
                                      · linarith only [h1, h1289, hlam]
                                      · linarith only [h1168, h1289, hlam]
                                  · linarith only [h1286, h2, hlam]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1, h1169, h1264, hc34, hlam, hphi, ht0b, ht45, ht5b, p1276_1, u0elo0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h0, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h4, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h905, hlam, p1276_1]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1079, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1, hlam, p1276_1]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h0, h1270, h1274, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1276_1]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h0, h1270, h1274, h4, h905, hc12, hc45, hlam, hphi, ht23, ht34, p1276_1]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1169, hlam, p1276_1]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h2, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h0, h905, hc12, hlam, hphi, p1276_1, u2elo3]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1168, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1256, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h3, hlam, p1276_0]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h0, h1079, hc12, hlam, hphi, p1276_1, u2elo4]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h1, h1079, h1264, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1276_1, u2elo4]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [h0, h1079, h905, hc12, hlam, hphi, p1276_1, u2elo4]
                                · have p1276_0 := h1276c.1
                                  have p1276_1 := h1276c.2.1
                                  have p1276_2 := h1276c.2.2.1
                                  have p1276_3 := h1276c.2.2.2
                                  linarith only [hlam, p1276_0]
                        · linarith only [h1, h1264, h1269, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1168, h1169, h1264, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1316 | h1316
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1317 | h1317
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1318 | h1318
            · linarith only [h0, h1316, h1318, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1320 | h1320
              · linarith only [h0, h1320, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1322 | h1322
                · linarith only [h0, h1079, h1322, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1324 | h1324
                  · linarith only [h1, h1079, h1168, h1316, h1324, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1326 | h1326
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1327 | h1327
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1328 | h1328
                        · linarith only [h1, h1168, h1326, h1328, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1330 | h1330
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1331 | h1331
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1332 | h1332
                              · rcases h0bigk with h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  rcases p1333_3 (m.d 0 1) (by simp) with h1335 | h1335
                                  · rcases p1333_3 (m.d 0 2) (by simp) with h1336 | h1336
                                    · linarith only [h0, h1336, hlam]
                                    · rcases p1333_3 (m.d 0 3) (by simp) with h1338 | h1338
                                      · linarith only [h1, h1338, hlam]
                                      · linarith only [h1338, h4, hlam]
                                  · linarith only [h0, h1335, hlam]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1, h1326, h1332, hc45, hlam, hphi, ht0b, ht5b, p1333_1, u0elo0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1, h1168, h1326, h1332, hc45, hlam, hphi, ht0b, ht5b, p1333_1, u0elo0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  rcases p1333_3 (m.d 0 1) (by simp) with h1344 | h1344
                                  · rcases p1333_3 (m.d 0 2) (by simp) with h1345 | h1345
                                    · linarith only [h0, h1345, hlam]
                                    · rcases p1333_3 (m.d 0 3) (by simp) with h1347 | h1347
                                      · linarith only [h1, h1347, hlam]
                                      · linarith only [h1316, h1347, hlam]
                                  · linarith only [h1344, h3, hlam]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h0, hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h4, hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h905, hlam, p1333_1]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1079, hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1, hlam, p1333_1]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h0, h4, hc12, hlam, hphi, p1333_1, u2elo2]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1168, hlam, p1333_1]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h0, h1079, h1328, h4, hc12, hlam, hphi, p1333_1, u2elo3]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h2, hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h0, h905, hc12, hlam, hphi, p1333_1, u2elo3]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1, h1326, h1332, h905, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1333_1, u2elo3]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h0, h1079, h905, hc12, hlam, hphi, p1333_1, u2elo3]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h3, hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h0, h1079, hc12, hlam, hphi, p1333_1, u2elo4]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1316, hlam, p1333_0]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [h1317, hlam, p1333_1]
                                · have p1333_0 := h1333c.1
                                  have p1333_1 := h1333c.2.1
                                  have p1333_2 := h1333c.2.2.1
                                  have p1333_3 := h1333c.2.2.2
                                  linarith only [hlam, p1333_0]
                              · linarith only [h0, h1328, h1332, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1327, h1331, h2, h905, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1, h1326, h1330, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1317, h1324, h1326, h1327, h905, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1168, h1316, h1318, h1326, h905, hc12, hlam, hphi, u2elo3]
          · linarith only [h1168, h1316, h1317, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1377 | h1377
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1378 | h1378
            · linarith only [h0, h1378, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1380 | h1380
              · linarith only [h0, h1380, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1382 | h1382
                · linarith only [h1, h1079, h1316, h1378, h1382, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
                  · linarith only [h1, h1168, h1384, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1386 | h1386
                    · linarith only [h1, h1316, h1386, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1388 | h1388
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1389 | h1389
                        · linarith only [h1168, h1389, h4, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1391 | h1391
                          · linarith only [h1, h1316, h1378, h1391, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1393 | h1393
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1394 | h1394
                              · rcases h0bigk with h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  rcases p1395_3 (m.d 0 1) (by simp) with h1397 | h1397
                                  · rcases p1395_3 (m.d 0 2) (by simp) with h1398 | h1398
                                    · linarith only [h0, h1398, hlam]
                                    · rcases p1395_3 (m.d 0 3) (by simp) with h1400 | h1400
                                      · linarith only [h1, h1400, hlam]
                                      · linarith only [h1400, h4, hlam]
                                  · linarith only [h0, h1397, hlam]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  rcases p1395_3 (m.d 0 1) (by simp) with h1404 | h1404
                                  · rcases p1395_3 (m.d 0 2) (by simp) with h1405 | h1405
                                    · linarith only [h0, h1405, hlam]
                                    · rcases p1395_3 (m.d 0 3) (by simp) with h1407 | h1407
                                      · linarith only [h1, h1407, hlam]
                                      · rcases p1395_3 (m.d 0 4) (by simp) with h1409 | h1409
                                        · linarith only [h1409, h2, hlam]
                                        · linarith only [h1168, h1409, hlam]
                                  · linarith only [h1, h1404, hlam]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h1388, h2, hc45, hlam, hphi, ht0b, ht5b, p1395_1, u0elo0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  rcases p1395_3 (m.d 0 1) (by simp) with h1414 | h1414
                                  · rcases p1395_3 (m.d 0 2) (by simp) with h1415 | h1415
                                    · linarith only [h0, h1415, hlam]
                                    · rcases p1395_3 (m.d 0 3) (by simp) with h1417 | h1417
                                      · linarith only [h1, h1417, hlam]
                                      · rcases p1395_3 (m.d 0 4) (by simp) with h1419 | h1419
                                        · linarith only [h1419, h2, hlam]
                                        · linarith only [h1377, h1419, hlam]
                                  · linarith only [h1414, h3, hlam]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h4, hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h905, hlam, p1395_1]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h1079, hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h1, hlam, p1395_1]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, h1391, h1394, h4, hc12, hc34, hlam, hphi, ht23, p1395_1]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h1168, hlam, p1395_1]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h1316, hlam, p1395_1]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h2, hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, h905, hc12, hlam, hphi, p1395_1, u2elo3]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, h4, h905, hc12, hlam, hphi, p1395_1, u2elo3]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, h1316, h4, h905, hc12, hlam, hphi, p1395_1, u2elo3]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h3, hlam, p1395_0]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, h1079, hc12, hlam, hphi, p1395_1, u2elo4]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h0, h1079, h4, hc12, hlam, hphi, p1395_1, u2elo4]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [h1377, hlam, p1395_1]
                                · have p1395_0 := h1395c.1
                                  have p1395_1 := h1395c.2.1
                                  have p1395_2 := h1395c.2.2.1
                                  have p1395_3 := h1395c.2.2.2
                                  linarith only [hlam, p1395_0]
                              · linarith only [h1388, h1394, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1388, h1393, h2, h905, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1377, h1380, h1388, h905, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
            · linarith only [h1446, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1448 | h1448
              · linarith only [h0, h1448, h905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1450 | h1450
                · linarith only [h0, h1079, h1450, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1452 | h1452
                  · linarith only [h1, h1168, h1452, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1454 | h1454
                    · linarith only [h1, h1316, h1454, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1456 | h1456
                      · linarith only [h1377, h1456, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1458 | h1458
                        · linarith only [h0, h1168, h1458, h4, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1460 | h1460
                          · linarith only [h0, h1316, h1460, h4, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1462 | h1462
                            · linarith only [h0, h1168, h1377, h1462, h4, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1464 | h1464
                              · linarith only [h0, h1458, h1462, h1464, h4, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1458, h1464, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1467 | h1467
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1468 | h1468
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1469 | h1469
      · linarith only [h0, h1469, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1471 | h1471
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1472 | h1472
          · linarith only [h1, h1472, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1474 | h1474
            · linarith only [h1474, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1477 | h1477
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1478 | h1478
                  · linarith only [h0, h1469, h1478, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1476, h1478, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h1468, h1476, h1477, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1467, h1469, h1476, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1483 | h1483
          · linarith only [h0, h1468, h1469, h1471, h1483, h3, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1485 | h1485
            · linarith only [h0, h1468, h1469, h1485, h3, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1487 | h1487
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1488 | h1488
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1489 | h1489
                  · linarith only [h0, h1469, h1489, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1489, h3, hc12, hlam, hphi, u2elo4]
                · linarith only [h1468, h1469, h1487, h1488, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1467, h1469, h1487, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1494 | h1494
      · linarith only [h0, h1468, h1494, h3, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1496 | h1496
        · linarith only [h1467, h1468, h1496, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1498 | h1498
          · linarith only [h1467, h1468, h1498, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1500 | h1500
            · linarith only [h1500, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1502 | h1502
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1503 | h1503
                · linarith only [h0, h1468, h1503, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1505 | h1505
                  · linarith only [h0, h1468, h1494, h1505, h2, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h1502, h1503, h1505, h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1467, h1468, h1502, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1509 | h1509
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1510 | h1510
      · linarith only [h0, h1467, h1510, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1512 | h1512
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1513 | h1513
          · linarith only [h1, h1513, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1515 | h1515
            · linarith only [h1, h1467, h1509, h1515, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1517 | h1517
              · linarith only [h1467, h1517, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1519 | h1519
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1520 | h1520
                  · linarith only [h1, h1510, h1517, h1520, h3, hlam]
                  · linarith only [h1, h1517, h1519, h1520, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1467, h1509, h1519, hc12, hlam, hphi, u2elo2]
        · linarith only [h1467, h1509, h1512, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1525 | h1525
      · linarith only [h0, h1467, h1525, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1527 | h1527
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1528 | h1528
          · linarith only [h1, h1528, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1530 | h1530
            · linarith only [h1, h1527, h1530, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1532 | h1532
              · linarith only [h1467, h1532, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1534 | h1534
                · linarith only [h1, h1509, h1532, h1534, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1536 | h1536
                  · linarith only [h0, h1525, h1536, h3, hlam]
                  · linarith only [h1534, h1536, h2, h3, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1539 | h1539
          · linarith only [h1527, h1539, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1541 | h1541
            · linarith only [h1541, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1543 | h1543
              · linarith only [h0, h1467, h1543, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1545 | h1545
                · linarith only [h0, h1509, h1545, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1547 | h1547
                  · linarith only [h0, h1467, h1525, h1547, h3, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1, h1543, h1547, h3, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1550 | h1550
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1551 | h1551
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1552 | h1552
      · linarith only [h0, h1552, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1554 | h1554
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1555 | h1555
          · linarith only [h0, h1551, h1555, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1557 | h1557
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1558 | h1558
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1559 | h1559
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1560 | h1560
                  · linarith only [h0, h1552, h1560, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1559, h1560, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1551, h1559, hc12, hlam, hphi, u2elo0]
              · linarith only [h1, h1557, h1558, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1565 | h1565
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1566 | h1566
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1567 | h1567
                  · linarith only [h0, h1552, h1567, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1566, h1567, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1551, h1566, hc12, hlam, hphi, u2elo0]
              · linarith only [h1550, h1565, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1572 | h1572
          · linarith only [h1, h1572, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1574 | h1574
            · linarith only [h1551, h1554, h1574, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1576 | h1576
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1577 | h1577
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1578 | h1578
                  · linarith only [h0, h1552, h1578, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1577, h1578, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1551, h1554, h1577, hc12, hlam, hphi, u2elo4]
              · linarith only [h1550, h1576, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1583 | h1583
      · linarith only [h0, h1551, h1583, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1585 | h1585
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1586 | h1586
          · linarith only [h1, h1586, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1588 | h1588
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1589 | h1589
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1590 | h1590
                · linarith only [h1551, h1590, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1592 | h1592
                  · linarith only [h1, h1583, h1590, h1592, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1592, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1551, h1585, h1589, h2, hc12, hlam, hphi, u2elo2]
            · linarith only [h1551, h1585, h1588, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1597 | h1597
          · linarith only [h1, h1597, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1599 | h1599
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1601 | h1601
                · linarith only [h0, h1551, h1601, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1603 | h1603
                  · linarith only [h0, h1583, h1603, h2, hlam]
                  · linarith only [h1, h1601, h1603, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1599, h1600, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1607 | h1607
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1608 | h1608
                · linarith only [h1551, h1608, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1610 | h1610
                  · linarith only [h0, h1583, h1610, h2, hlam]
                  · linarith only [h1, h1608, h1610, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1550, h1607, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1614 | h1614
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1615 | h1615
      · linarith only [h0, h1615, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1617 | h1617
        · linarith only [h0, h1550, h1615, h1617, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1619 | h1619
          · linarith only [h0, h1614, h1615, h1619, h2, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1621 | h1621
            · linarith only [h0, h1550, h1614, h1615, h1621, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1623 | h1623
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1624 | h1624
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1625 | h1625
                  · linarith only [h0, h1615, h1625, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1624, h1625, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1550, h1614, h1615, h1623, h1624, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1629 | h1629
                · linarith only [h0, h1623, h1629, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1614, h1615, h1629, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1632 | h1632
      · linarith only [h0, h1614, h1632, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1634 | h1634
        · linarith only [h1, h1550, h1614, h1634, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1636 | h1636
          · linarith only [h1, h1636, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1638 | h1638
            · linarith only [h1, h1550, h1638, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1640 | h1640
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
                · linarith only [h1614, h1641, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1643 | h1643
                  · linarith only [h1, h1632, h1641, h1643, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1643, h2, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1646 | h1646
                · linarith only [h0, h1614, h1646, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1648 | h1648
                  · linarith only [h1, h1640, h1646, h1648, h2, hc24, hc45, hlam, hphi]
                  · linarith only [h1, h1646, h1648, h2, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1651 | h1651
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1652 | h1652
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1653 | h1653
      · linarith only [h0, h1, h1653, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1655 | h1655
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1656 | h1656
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1657 | h1657
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1658 | h1658
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1659 | h1659
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1660 | h1660
                  · linarith only [h0, h1653, h1660, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1660, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1663 | h1663
                  · linarith only [h0, h1, h1653, h1663, hlam]
                  · linarith only [h0, h1, h1663, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h1656, h1658, hlam]
            · linarith only [h1, h1651, h1657, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1668 | h1668
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1669 | h1669
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1670 | h1670
                · linarith only [h1655, h1656, h1670, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1672 | h1672
                  · linarith only [h1653, h1672, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1, h1672, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1652, h1669, hlam]
            · linarith only [h1, h1652, h1655, h1656, h1668, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1677 | h1677
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1678 | h1678
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1679 | h1679
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1680 | h1680
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1681 | h1681
                  · linarith only [h0, h1653, h1681, hlam]
                  · linarith only [h0, h1, h1681, hc12, hlam, hphi, u2elo2]
                · linarith only [h1655, h1677, h1680, hlam]
              · linarith only [h0, h1, h1655, h1677, h1679, hc12, hlam, hphi, u2elo3]
            · linarith only [h1, h1651, h1678, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1687 | h1687
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1688 | h1688
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1689 | h1689
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1690 | h1690
                  · linarith only [h0, h1653, h1690, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1690, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1693 | h1693
                  · linarith only [h0, h1, h1653, h1693, hlam]
                  · linarith only [h0, h1, h1693, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1652, h1688, hlam]
            · linarith only [h1, h1651, h1687, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1698 | h1698
      · linarith only [h0, h1, h1698, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1700 | h1700
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1701 | h1701
          · linarith only [h0, h1652, h1701, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1703 | h1703
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1704 | h1704
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1705 | h1705
                · linarith only [h0, h1652, h1700, h1705, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1707 | h1707
                  · linarith only [h0, h1698, h1707, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1707, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1710 | h1710
                · linarith only [h0, h1, h1700, h1704, h1710, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1712 | h1712
                  · linarith only [h0, h1, h1704, h1712, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1712, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h1698, h1700, h1703, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1716 | h1716
          · linarith only [h1651, h1652, h1700, h1716, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1718 | h1718
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1719 | h1719
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1720 | h1720
                · linarith only [h1651, h1652, h1720, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1722 | h1722
                  · linarith only [h0, h1698, h1722, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1722, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1725 | h1725
                · linarith only [h1, h1651, h1719, h1725, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1727 | h1727
                  · linarith only [h0, h1, h1719, h1727, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1727, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h1651, h1718, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1731 | h1731
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1732 | h1732
      · linarith only [h0, h1, h1732, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1734 | h1734
        · linarith only [h0, h1651, h1734, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1736 | h1736
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1737 | h1737
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1738 | h1738
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1739 | h1739
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1740 | h1740
                  · linarith only [h0, h1732, h1740, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1740, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1651, h1736, h1739, hlam]
              · linarith only [h0, h1, h1736, h1738, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1745 | h1745
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1746 | h1746
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1747 | h1747
                  · linarith only [h0, h1, h1737, h1747, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1747, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h1734, h1736, h1737, h1746, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1, h1734, h1736, h1745, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1752 | h1752
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1753 | h1753
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1754 | h1754
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1755 | h1755
                  · linarith only [h0, h1732, h1755, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1755, hc12, hlam, hphi, u2elo2]
                · linarith only [h1651, h1731, h1754, hlam]
              · linarith only [h1, h1731, h1753, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1760 | h1760
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1761 | h1761
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1762 | h1762
                  · linarith only [h0, h1, h1752, h1762, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1762, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h1731, h1752, h1761, hlam]
              · linarith only [h1, h1731, h1760, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1767 | h1767
      · linarith only [h0, h1, h1767, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1769 | h1769
        · linarith only [h0, h1651, h1769, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1771 | h1771
          · linarith only [h0, h1731, h1771, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1773 | h1773
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1774 | h1774
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1775 | h1775
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1776 | h1776
                  · linarith only [h0, h1767, h1776, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1776, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1779 | h1779
                  · linarith only [h0, h1, h1767, h1773, h1779, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h1779, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1782 | h1782
                · linarith only [h1773, h1774, h1782, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1784 | h1784
                  · linarith only [h0, h1651, h1773, h1774, h1784, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1784, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1787 | h1787
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1788 | h1788
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1789 | h1789
                  · linarith only [h0, h1731, h1773, h1787, h1789, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1789, hc12, hlam, hphi, u2elo2]
                · linarith only [h1773, h1787, h1788, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1793 | h1793
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                  · linarith only [h0, h1, h1773, h1794, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1794, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1797 | h1797
                  · linarith only [h0, h1, h1773, h1797, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1797, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
