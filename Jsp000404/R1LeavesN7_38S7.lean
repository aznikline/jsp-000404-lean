import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h892 | h892
  · rcases m.htr 0 2 5 (by decide) (by decide) with h893 | h893
    · rcases m.htr 0 3 4 (by decide) (by decide) with h894 | h894
      · rcases m.htr 0 3 5 (by decide) (by decide) with h895 | h895
        · rcases m.htr 0 4 5 (by decide) (by decide) with h896 | h896
          · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
            · linarith only [h0, h4, h892, h897, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
              · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
                · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h902 | h902
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h903 | h903
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h904 | h904
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h905 | h905
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h906 | h906
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h907 | h907
                              · rcases h0bigk with h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h0, h899, h904, h907, hc01, hc45, hlam, hphi, ht0b, ht5b, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h0, h4, h899, h904, h907, hc01, hc45, hlam, hphi, ht0b, ht5b, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h2, h899, h904, h907, hc01, hc45, hlam, hphi, ht0b, ht5b, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  rcases p908_3 (m.d 0 1) (by simp) with h913 | h913
                                  · rcases p908_3 (m.d 0 2) (by simp) with h914 | h914
                                    · linarith only [h0, h914, hlam]
                                    · linarith only [h893, h914, hlam]
                                  · linarith only [h3, h913, hlam]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h0, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h4, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h2, h899, h904, h907, hc02, hc45, hlam, hphi, ht0b, ht5b, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h1, hlam, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h4, hc02, hc23, hlam, hphi, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h2, h4, h899, h904, h907, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  rcases p908_3 (m.d 0 1) (by simp) with h927 | h927
                                  · rcases p908_3 (m.d 0 2) (by simp) with h928 | h928
                                    · linarith only [h4, h928, hlam]
                                    · linarith only [h893, h928, hlam]
                                  · linarith only [h3, h927, hlam]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h2, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h892, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h894, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h3, h900, h905, h907, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p908_1, u4elo0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h3, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h893, hlam, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h895, hlam, p908_0]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [h896, hlam, p908_1]
                                · have p908_0 := h908c.1
                                  have p908_1 := h908c.2.1
                                  have p908_2 := h908c.2.2.1
                                  have p908_3 := h908c.2.2.2
                                  linarith only [hlam, p908_0]
                              · linarith only [h899, h906, h907, hc34, hlam, hphi, u4elo1]
                            · linarith only [h896, h906, hc24, hlam, hphi, u4elo0]
                          · linarith only [h4, h895, h905, hlam]
                        · linarith only [h4, h904, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h896, h901, h903, hc34, hlam, hphi, u4elo0]
                    · linarith only [h895, h896, h897, h899, h902, hc24, hlam, hphi, u4elo0]
                  · linarith only [h897, h899, h901, hc24, hlam, hphi, u4elo3]
                · linarith only [h4, h893, h899, h900, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h4, h892, h899, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h951 | h951
            · linarith only [h0, h4, h893, h951, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h953 | h953
              · rcases m.htr 1 2 5 (by decide) (by decide) with h954 | h954
                · rcases m.htr 1 3 4 (by decide) (by decide) with h955 | h955
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h957 | h957
                      · linarith only [h896, h957, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h959 | h959
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h960 | h960
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h961 | h961
                            · linarith only [h2, h896, h953, h961, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                              · linarith only [h2, h896, h953, h959, h963, hlam]
                              · rcases h0bigk with h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h0, h954, hc01, hc25, hlam, hphi, ht0b, ht5b, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h0, h4, h954, h960, hc01, hc35, hlam, hphi, ht0b, ht5b, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  rcases p965_3 (m.d 0 1) (by simp) with h969 | h969
                                  · rcases p965_3 (m.d 0 2) (by simp) with h970 | h970
                                    · linarith only [h0, h970, hlam]
                                    · linarith only [h892, h970, hlam]
                                  · linarith only [h2, h969, hlam]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  rcases p965_3 (m.d 0 1) (by simp) with h974 | h974
                                  · rcases p965_3 (m.d 0 2) (by simp) with h975 | h975
                                    · linarith only [h0, h975, hlam]
                                    · linarith only [h893, h975, hlam]
                                  · linarith only [h3, h974, hlam]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h0, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h4, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h2, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h1, hlam, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h0, h954, h959, h961, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  rcases p965_3 (m.d 0 1) (by simp) with h987 | h987
                                  · rcases p965_3 (m.d 0 2) (by simp) with h988 | h988
                                    · linarith only [h4, h988, hlam]
                                    · linarith only [h892, h988, hlam]
                                  · linarith only [h2, h987, hlam]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  rcases p965_3 (m.d 0 1) (by simp) with h992 | h992
                                  · rcases p965_3 (m.d 0 2) (by simp) with h993 | h993
                                    · linarith only [h4, h993, hlam]
                                    · linarith only [h893, h993, hlam]
                                  · linarith only [h3, h992, hlam]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h2, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h892, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h894, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h896, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h3, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h893, hlam, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h895, hlam, p965_0]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [h2, h4, h893, h953, h959, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p965_1]
                                · have p965_0 := h965c.1
                                  have p965_1 := h965c.2.1
                                  have p965_2 := h965c.2.2.1
                                  have p965_3 := h965c.2.2.2
                                  linarith only [hlam, p965_0]
                          · linarith only [h4, h895, h960, hlam]
                        · linarith only [h4, h959, hc02, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h895, h896, h951, h953, h956, hc24, hlam, hphi, u4elo4]
                  · linarith only [h951, h953, h955, hc24, hlam, hphi, u4elo3]
                · linarith only [h4, h893, h953, h954, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h4, h892, h953, hc12, hc23, hlam, hphi]
        · linarith only [h4, h893, h895, hlam]
      · linarith only [h4, h892, h894, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1015 | h1015
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1016 | h1016
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1017 | h1017
          · linarith only [h1017, h892, h893, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1019 | h1019
            · linarith only [h0, h1019, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1021 | h1021
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1022 | h1022
                · linarith only [h0, h1022, h893, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1024 | h1024
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1025 | h1025
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1026 | h1026
                      · linarith only [h1017, h1026, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1028 | h1028
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1029 | h1029
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1030 | h1030
                            · linarith only [h1017, h1030, hc04, hlam, hphi, u4elo2]
                            · linarith only [h1028, h1030, h892, h893, hc34, hlam, hphi, u4elo4]
                          · linarith only [h0, h1, h1021, h1025, h1028, h1029, h4, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1021, h1028, h4, hc24, hlam, hphi, u4elo3]
                    · linarith only [h1016, h1017, h1019, h1021, h1025, hc24, hlam, hphi, u4elo4]
                  · linarith only [h1019, h1021, h1024, hc24, hlam, hphi, u4elo3]
              · linarith only [h1021, h4, h892, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1038 | h1038
          · linarith only [h1016, h1038, h4, h892, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1040 | h1040
            · linarith only [h0, h1040, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1042 | h1042
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1043 | h1043
                · linarith only [h0, h1043, h893, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1045 | h1045
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1046 | h1046
                    · linarith only [h1, h1016, h1046, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1048 | h1048
                      · linarith only [h1038, h1048, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1050 | h1050
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1051 | h1051
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1052 | h1052
                            · linarith only [h1038, h1052, hc04, hlam, hphi, u4elo2]
                            · linarith only [h0, h1016, h1042, h1050, h1051, h1052, h4, hc34, hlam, hphi, u4elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1055 | h1055
                            · linarith only [h1038, h1055, h2, hc14, hlam, hphi, u4elo2]
                            · linarith only [h0, h1042, h1050, h1051, h1055, h4, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1050, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1015, h1016, h1038, h1045, hc13, hlam, hphi, ht34, u4elo4]
              · linarith only [h1042, h4, h892, hc12, hc23, hlam, hphi]
      · linarith only [h1015, h4, h892, hc24, hlam, hphi, u4elo3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1062 | h1062
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1063 | h1063
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1064 | h1064
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1065 | h1065
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1066 | h1066
            · linarith only [h0, h1062, h1066, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1068 | h1068
              · linarith only [h0, h1068, h892, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1070 | h1070
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1071 | h1071
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1072 | h1072
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1073 | h1073
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1075 | h1075
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1076 | h1076
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1077 | h1077
                              · rcases h0bigk with h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, h1070, h1075, h1077, hc01, hc45, hlam, hphi, ht0b, ht5b, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1, h1071, h1077, hc01, hc45, hlam, hphi, ht0b, ht5b, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1068, h1070, h1075, h1077, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  rcases p1078_3 (m.d 0 1) (by simp) with h1083 | h1083
                                  · rcases p1078_3 (m.d 0 2) (by simp) with h1084 | h1084
                                    · linarith only [h0, h1084, hlam]
                                    · linarith only [h1062, h1084, hlam]
                                  · linarith only [h1083, h3, hlam]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h4, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h892, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1074, h3, h892, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h4, hc02, hc23, hlam, hphi, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, h1070, h1075, h4, h892, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  rcases p1078_3 (m.d 0 1) (by simp) with h1097 | h1097
                                  · rcases p1078_3 (m.d 0 2) (by simp) with h1098 | h1098
                                    · linarith only [h1098, h4, hlam]
                                    · linarith only [h1062, h1098, hlam]
                                  · linarith only [h1097, h3, hlam]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h2, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, h1070, h1075, h1077, hc04, hc45, hlam, hphi, ht0b, ht5b, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1063, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1070, h1075, h1077, h3, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo2]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h3, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1062, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1064, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1065, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                              · linarith only [h1065, h1077, h892, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1076, h892, hc02, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1064, h1075, h4, hlam]
                        · linarith only [h0, h1070, h1074, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h1065, h1073, hc14, hlam, hphi, u4elo0]
                    · linarith only [h1062, h1064, h1071, h1072, h892, hc34, hlam, hphi, u4elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1121 | h1121
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1122 | h1122
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1123 | h1123
                              · rcases h0bigk with h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h0, h1070, h1121, h1123, hc01, hc45, hlam, hphi, ht0b, ht5b, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1063, h1066, h1070, h1071, h1121, h1123, hc01, hc45, hlam, hphi, ht0b, ht5b, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1063, h1066, h1070, h1071, h1121, h1123, hc01, hc45, hlam, hphi, ht0b, ht5b, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  rcases p1124_3 (m.d 0 1) (by simp) with h1129 | h1129
                                  · rcases p1124_3 (m.d 0 2) (by simp) with h1130 | h1130
                                    · linarith only [h0, h1130, hlam]
                                    · linarith only [h1062, h1130, hlam]
                                  · linarith only [h1129, h3, hlam]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h0, hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h4, hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h892, hlam, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1, hlam, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h0, h1070, h1121, h1123, hc03, hc45, hlam, hphi, ht0b, ht5b, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1063, h1066, h1070, h1071, h1121, h1123, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  rcases p1124_3 (m.d 0 1) (by simp) with h1143 | h1143
                                  · rcases p1124_3 (m.d 0 2) (by simp) with h1144 | h1144
                                    · linarith only [h1144, h4, hlam]
                                    · linarith only [h1062, h1144, hlam]
                                  · linarith only [h1143, h3, hlam]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h2, hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h0, h1070, h1121, h1123, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1124_1, u4elo2]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1063, hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1070, h1121, h1123, h3, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1124_1, u4elo2]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h3, hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1062, hlam, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1064, hlam, p1124_0]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [h1065, hlam, p1124_1]
                                · have p1124_0 := h1124c.1
                                  have p1124_1 := h1124c.2.1
                                  have p1124_2 := h1124c.2.2.1
                                  have p1124_3 := h1124c.2.2.2
                                  linarith only [hlam, p1124_0]
                              · linarith only [h1066, h1070, h1071, h1121, h1123, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h0, h1070, h1121, h1122, h892, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h1063, h1066, h1070, h1071, h1121, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1063, h1120, h4, hlam]
                      · linarith only [h1065, h1066, h1070, h1071, h1119, h892, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h1062, h1064, h1066, h1070, h1118, h892, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                · linarith only [h1062, h1070, h892, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h1062, h1065, h892, hlam]
        · linarith only [h1062, h1064, h4, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1167 | h1167
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1169 | h1169
            · linarith only [h0, h1062, h1169, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1171 | h1171
              · linarith only [h0, h1062, h1171, h892, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1173 | h1173
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1174 | h1174
                  · linarith only [h1, h1063, h1167, h1174, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1176 | h1176
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1177 | h1177
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1178 | h1178
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1179 | h1179
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1180 | h1180
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1181 | h1181
                              · rcases h0bigk with h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h0, h1173, h1179, h1181, hc01, hc45, hlam, hphi, ht0b, ht5b, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h0, h1173, h1179, h1181, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1169, h1173, h1174, h1179, h1181, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  rcases p1182_3 (m.d 0 1) (by simp) with h1187 | h1187
                                  · rcases p1182_3 (m.d 0 2) (by simp) with h1188 | h1188
                                    · linarith only [h0, h1188, hlam]
                                    · linarith only [h1062, h1188, hlam]
                                  · linarith only [h1187, h3, hlam]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h0, hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h4, hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h892, hlam, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1063, h1178, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1, hlam, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1063, h1178, hc02, hc23, hlam, hphi, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1063, hlam, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1062, h1063, h1179, h1181, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1182_1, u4elo0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h2, hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h0, h1173, h1179, h1181, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1182_1, u4elo2]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h892, hc03, hlam, hphi, ht34, p1182_1, u4elo2]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1062, h1063, h1178, h1179, h1181, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1182_1, u4elo2]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h3, hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1062, hlam, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1167, hlam, p1182_0]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [h1168, hlam, p1182_1]
                                · have p1182_0 := h1182c.1
                                  have p1182_1 := h1182c.2.1
                                  have p1182_2 := h1182c.2.2.1
                                  have p1182_3 := h1182c.2.2.2
                                  linarith only [hlam, p1182_0]
                              · linarith only [h1, h1063, h1169, h1173, h1179, h1181, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h0, h1173, h1179, h1180, h892, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h1063, h1167, h1178, h1179, hc23, hlam, hphi, ht34, u4elo2]
                        · linarith only [h1178, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1168, h1169, h1174, h1177, hc12, hlam, hphi, ht23, ht34, u4elo0]
                    · linarith only [h1063, h1167, h1169, h1173, h1176, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h1062, h1063, h1173, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h1062, h1063, h1168, h4, hlam]
        · linarith only [h1062, h1167, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1221 | h1221
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1222 | h1222
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1223 | h1223
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1224 | h1224
            · linarith only [h0, h1224, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1226 | h1226
              · linarith only [h0, h1226, h892, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1228 | h1228
                · linarith only [h0, h1062, h1228, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1231 | h1231
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1232 | h1232
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1234 | h1234
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1235 | h1235
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1236 | h1236
                              · rcases h0bigk with h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  rcases p1237_3 (m.d 0 1) (by simp) with h1239 | h1239
                                  · rcases p1237_3 (m.d 0 2) (by simp) with h1240 | h1240
                                    · linarith only [h0, h1240, hlam]
                                    · rcases p1237_3 (m.d 0 3) (by simp) with h1242 | h1242
                                      · linarith only [h1, h1242, hlam]
                                      · linarith only [h1242, h4, hlam]
                                  · linarith only [h0, h1239, hlam]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1, h1230, h1236, hc01, hc45, hlam, hphi, ht0b, ht5b, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1230, h1236, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  rcases p1237_3 (m.d 0 1) (by simp) with h1248 | h1248
                                  · rcases p1237_3 (m.d 0 2) (by simp) with h1249 | h1249
                                    · linarith only [h0, h1249, hlam]
                                    · rcases p1237_3 (m.d 0 3) (by simp) with h1251 | h1251
                                      · linarith only [h1, h1251, hlam]
                                      · linarith only [h1222, h1251, hlam]
                                  · linarith only [h1248, h3, hlam]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h0, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h4, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h892, hlam, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1062, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1, hlam, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h4, hc02, hc23, hlam, hphi, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1230, h1236, h2, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1228, h3, h4, hc12, hc23, hlam, hphi, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h2, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1237_1, u4elo0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1221, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1228, h3, h892, hc12, hlam, hphi, ht23, ht34, p1237_1, u4elo2]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h3, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h0, h1062, h1235, hc12, hlam, hphi, ht23, ht34, p1237_1, u4elo2]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1222, hlam, p1237_0]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [h1223, hlam, p1237_1]
                                · have p1237_0 := h1237c.1
                                  have p1237_1 := h1237c.2.1
                                  have p1237_2 := h1237c.2.2.1
                                  have p1237_3 := h1237c.2.2.2
                                  linarith only [hlam, p1237_0]
                              · linarith only [h1223, h1236, hc34, hlam, hphi, u4elo0]
                            · linarith only [h1, h1230, h1232, h1235, h892, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1231, h1232, h1234, h2, h4, h892, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h1, h1230, h1233, h4, hlam]
                      · linarith only [h1223, h1232, h892, hc14, hlam, hphi, u4elo2]
                    · linarith only [h1222, h1223, h1230, h1231, h892, hc34, hlam, hphi, u4elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1281 | h1281
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1282 | h1282
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1283 | h1283
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1284 | h1284
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1285 | h1285
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1286 | h1286
                              · rcases h0bigk with h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c | h1287c
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  rcases p1287_3 (m.d 0 1) (by simp) with h1289 | h1289
                                  · rcases p1287_3 (m.d 0 2) (by simp) with h1290 | h1290
                                    · linarith only [h0, h1290, hlam]
                                    · rcases p1287_3 (m.d 0 3) (by simp) with h1292 | h1292
                                      · linarith only [h1, h1292, hlam]
                                      · linarith only [h1292, h4, hlam]
                                  · linarith only [h0, h1289, hlam]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1221, h1230, h1281, h1286, hc01, hc45, hlam, hphi, ht0b, ht5b, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1221, h1230, h1281, h1286, hc01, hc45, hlam, hphi, ht0b, ht5b, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  rcases p1287_3 (m.d 0 1) (by simp) with h1298 | h1298
                                  · rcases p1287_3 (m.d 0 2) (by simp) with h1299 | h1299
                                    · linarith only [h0, h1299, hlam]
                                    · rcases p1287_3 (m.d 0 3) (by simp) with h1301 | h1301
                                      · linarith only [h1, h1301, hlam]
                                      · linarith only [h1222, h1301, hlam]
                                  · linarith only [h1298, h3, hlam]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h0, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h4, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h892, hlam, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1062, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1, hlam, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1221, h1230, h1281, h1286, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h0, h1062, h4, hc12, hc23, hlam, hphi, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h2, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h0, h892, hc12, hlam, hphi, ht23, ht34, p1287_1, u4elo2]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1221, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h0, h1062, h892, hc12, hlam, hphi, ht23, ht34, p1287_1, u4elo2]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h3, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h0, h1062, hc12, hc25, hlam, hphi, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1222, hlam, p1287_0]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [h1223, hlam, p1287_1]
                                · have p1287_0 := h1287c.1
                                  have p1287_1 := h1287c.2.1
                                  have p1287_2 := h1287c.2.2.1
                                  have p1287_3 := h1287c.2.2.2
                                  linarith only [hlam, p1287_0]
                              · linarith only [h1230, h1281, h1286, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h0, h1285, h892, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1230, h1281, h1284, h4, hc03, hc34, hlam, hphi]
                        · linarith only [h1221, h1283, h4, hlam]
                      · linarith only [h1223, h1230, h1282, h892, hc13, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1330 | h1330
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1331 | h1331
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1332 | h1332
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1333 | h1333
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1334 | h1334
                              · rcases h0bigk with h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  rcases p1335_3 (m.d 0 1) (by simp) with h1337 | h1337
                                  · rcases p1335_3 (m.d 0 2) (by simp) with h1338 | h1338
                                    · linarith only [h0, h1338, hlam]
                                    · rcases p1335_3 (m.d 0 3) (by simp) with h1340 | h1340
                                      · linarith only [h1, h1340, hlam]
                                      · linarith only [h1340, h4, hlam]
                                  · linarith only [h0, h1337, hlam]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1221, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1330, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1222, h1224, h1281, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h0, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h4, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h892, hlam, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1062, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1, hlam, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1330, h2, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1224, h1281, h3, h4, hc12, hc23, hlam, hphi, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h2, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1335_1, u4elo0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1221, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1222, h1224, h1281, h892, hc12, hlam, hphi, ht23, ht34, p1335_1, u4elo2]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h3, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h0, h1062, hc12, hc25, hlam, hphi, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1222, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1223, hlam, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                              · linarith only [h1224, h1230, h1334, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h1223, h1330, h1333, h3, h892, hlam]
                          · linarith only [h0, h1222, h1223, h1332, h4, hc12, hlam, hphi, ht23, ht34, u4elo0]
                        · linarith only [h1221, h1331, h4, hlam]
                      · linarith only [h1223, h1330, h892, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
            · linarith only [h0, h1372, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
              · linarith only [h0, h1223, h1374, h892, hc24, hlam, hphi, u4elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1376 | h1376
                · linarith only [h0, h1062, h1376, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1378 | h1378
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1379 | h1379
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1380 | h1380
                      · linarith only [h1223, h1380, h892, hc02, hlam, hphi, ht23, ht34, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1382 | h1382
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1383 | h1383
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1384 | h1384
                            · linarith only [h0, h1223, h1384, h892, hc12, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h1384, h892, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1222, h1383, h4, hlam]
                        · linarith only [h1, h1378, h1382, h4, hlam]
                    · linarith only [h1222, h1223, h1378, h1379, hc34, hlam, hphi, u4elo4]
                  · linarith only [h1221, h1223, h1378, hc13, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1391 | h1391
          · linarith only [h1221, h1222, h1391, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1393 | h1393
            · linarith only [h0, h1391, h1393, h892, hc23, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1395 | h1395
              · linarith only [h0, h1391, h1395, h892, hc24, hlam, hphi, u4elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1397 | h1397
                · linarith only [h0, h1062, h1397, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1399 | h1399
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1400 | h1400
                    · linarith only [h1, h1222, h1400, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1402 | h1402
                      · linarith only [h1391, h1402, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1404 | h1404
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1405 | h1405
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1406 | h1406
                            · linarith only [h1391, h1406, h892, hc02, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h1406, h892, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1409 | h1409
                            · linarith only [h0, h1391, h1409, h892, hc12, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h1409, h892, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h1404, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1221, h1222, h1391, h1399, hc13, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1414 | h1414
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1415 | h1415
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1416 | h1416
            · linarith only [h0, h1062, h1221, h1414, h1416, hc23, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1418 | h1418
              · linarith only [h0, h1062, h1221, h1414, h1418, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1420 | h1420
                · linarith only [h0, h1062, h1420, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1422 | h1422
                  · linarith only [h1, h1221, h1422, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1424 | h1424
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1425 | h1425
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1426 | h1426
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1427 | h1427
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1428 | h1428
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1429 | h1429
                              · rcases h0bigk with h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  rcases p1430_3 (m.d 0 1) (by simp) with h1432 | h1432
                                  · rcases p1430_3 (m.d 0 2) (by simp) with h1433 | h1433
                                    · linarith only [h0, h1433, hlam]
                                    · rcases p1430_3 (m.d 0 3) (by simp) with h1435 | h1435
                                      · linarith only [h1, h1435, hlam]
                                      · linarith only [h1435, h4, hlam]
                                  · linarith only [h0, h1432, hlam]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1, h1424, h1429, hc01, hc45, hlam, hphi, ht0b, ht5b, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1, h1221, h1424, h1429, hc01, hc45, hlam, hphi, ht0b, ht5b, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  rcases p1430_3 (m.d 0 1) (by simp) with h1441 | h1441
                                  · rcases p1430_3 (m.d 0 2) (by simp) with h1442 | h1442
                                    · linarith only [h0, h1442, hlam]
                                    · rcases p1430_3 (m.d 0 3) (by simp) with h1444 | h1444
                                      · linarith only [h1, h1444, hlam]
                                      · linarith only [h1414, h1444, hlam]
                                  · linarith only [h1441, h3, hlam]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h0, hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h4, hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h892, hlam, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1062, hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1, hlam, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h0, h1221, h1426, hc12, hlam, hphi, ht23, ht34, p1430_1, u4elo2]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1221, hlam, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h0, h1062, h1221, h1426, hc12, hlam, hphi, ht23, ht34, p1430_1, u4elo2]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h2, hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1430_1, u4elo0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1, h1221, h1424, h1426, h1429, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1430_1, u4elo2]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h0, h1062, h1221, h1426, hc12, hlam, hphi, ht23, ht34, p1430_1, u4elo2]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h3, hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h0, h1062, hc12, hc25, hlam, hphi, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1414, hlam, p1430_0]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [h1415, hlam, p1430_1]
                                · have p1430_0 := h1430c.1
                                  have p1430_1 := h1430c.2.1
                                  have p1430_2 := h1430c.2.2.1
                                  have p1430_3 := h1430c.2.2.2
                                  linarith only [hlam, p1430_0]
                              · linarith only [h1, h1221, h1424, h1429, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h1221, h1414, h1425, h1428, h3, hc24, hlam, hphi, u4elo3]
                          · linarith only [h1, h1221, h1424, h1426, h1427, hlam]
                        · linarith only [h0, h1426, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1415, h1425, h892, hc14, hlam, hphi, u4elo2]
                    · linarith only [h1221, h1414, h1424, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h1221, h1414, h1415, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1475 | h1475
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
            · linarith only [h0, h1476, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1478 | h1478
              · linarith only [h1, h1414, h1476, h1478, h892, hc02, hc35, hlam, hphi, ht23]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1480 | h1480
                · linarith only [h0, h1062, h1480, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
                  · linarith only [h1, h1221, h1482, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1484 | h1484
                    · linarith only [h1414, h1482, h1484, hc03, hlam, hphi, ht34, u4elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1486 | h1486
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1487 | h1487
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1488 | h1488
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1489 | h1489
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1490 | h1490
                              · rcases h0bigk with h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  rcases p1491_3 (m.d 0 1) (by simp) with h1493 | h1493
                                  · rcases p1491_3 (m.d 0 2) (by simp) with h1494 | h1494
                                    · linarith only [h0, h1494, hlam]
                                    · rcases p1491_3 (m.d 0 3) (by simp) with h1496 | h1496
                                      · linarith only [h1, h1496, hlam]
                                      · linarith only [h1496, h4, hlam]
                                  · linarith only [h0, h1493, hlam]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  rcases p1491_3 (m.d 0 1) (by simp) with h1500 | h1500
                                  · rcases p1491_3 (m.d 0 2) (by simp) with h1501 | h1501
                                    · linarith only [h0, h1501, hlam]
                                    · rcases p1491_3 (m.d 0 3) (by simp) with h1503 | h1503
                                      · linarith only [h1, h1503, hlam]
                                      · rcases p1491_3 (m.d 0 4) (by simp) with h1505 | h1505
                                        · linarith only [h1505, h2, hlam]
                                        · linarith only [h1221, h1505, hlam]
                                  · linarith only [h1, h1500, hlam]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1475, hc01, hc45, hlam, hphi, ht0b, ht5b, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  rcases p1491_3 (m.d 0 1) (by simp) with h1510 | h1510
                                  · rcases p1491_3 (m.d 0 2) (by simp) with h1511 | h1511
                                    · linarith only [h0, h1511, hlam]
                                    · rcases p1491_3 (m.d 0 3) (by simp) with h1513 | h1513
                                      · linarith only [h1, h1513, hlam]
                                      · rcases p1491_3 (m.d 0 4) (by simp) with h1515 | h1515
                                        · linarith only [h1515, h2, hlam]
                                        · linarith only [h1475, h1515, hlam]
                                  · linarith only [h1510, h3, hlam]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h4, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h892, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1062, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, h1414, h1488, hc12, hc25, hlam, hphi, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1221, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1414, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h2, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1491_1, u4elo0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1221, h1487, hc03, hlam, hphi, ht34, p1491_1, u4elo2]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1, h1221, h1414, h1476, h1487, hc12, hlam, hphi, ht23, ht34, p1491_1, u4elo2]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h3, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, h1062, hc12, hc25, hlam, hphi, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1, h1414, h1476, h1488, hc12, hc25, hlam, hphi, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1475, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                              · linarith only [h1, h1221, h1476, h1490, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h1486, h1489, h2, hc24, hlam, hphi, u4elo0]
                          · linarith only [h1, h1221, h1476, h1487, h1488, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1487, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1475, h1486, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1544 | h1544
            · linarith only [h0, h1544, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1546 | h1546
              · linarith only [h0, h1546, h892, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1548 | h1548
                · linarith only [h0, h1062, h1548, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1550 | h1550
                  · linarith only [h1, h1221, h1475, h1550, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1552 | h1552
                    · linarith only [h1, h1414, h1552, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1554 | h1554
                      · linarith only [h1475, h1554, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1556 | h1556
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1557 | h1557
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1558 | h1558
                            · linarith only [h0, h1221, h1475, h1558, h4, hc12, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h1558, h892, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h1221, h1556, h1557, h4, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1556, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1563 | h1563
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1564 | h1564
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1565 | h1565
      · linarith only [h0, h1565, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1567 | h1567
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1568 | h1568
          · linarith only [h1, h1568, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1570 | h1570
            · linarith only [h1570, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1572 | h1572
              · linarith only [h0, h1570, h1572, h3, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h1563, h1570, h1572, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1575 | h1575
          · linarith only [h1567, h1575, h2, h3, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1577 | h1577
            · linarith only [h0, h1564, h1577, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1579 | h1579
              · linarith only [h0, h1577, h1579, h3, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h1563, h1577, h1579, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h1563, h1564, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1583 | h1583
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1584 | h1584
      · linarith only [h0, h1584, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1586 | h1586
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1587 | h1587
          · linarith only [h1, h1587, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1589 | h1589
            · linarith only [h1589, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1591 | h1591
              · linarith only [h0, h1563, h1591, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1593 | h1593
                · linarith only [h1, h1589, h1591, h1593, h3, hc24, hlam, hphi, u4elo4]
                · linarith only [h1563, h1583, h1593, hc12, hc23, hlam, hphi]
        · linarith only [h1563, h1583, h1586, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1597 | h1597
      · linarith only [h0, h1583, h1597, h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1599 | h1599
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1600 | h1600
          · linarith only [h1, h1600, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1602 | h1602
            · linarith only [h1602, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1604 | h1604
              · linarith only [h0, h1563, h1604, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1606 | h1606
                · linarith only [h0, h1602, h1606, h3, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1608 | h1608
                  · linarith only [h0, h1597, h1608, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1610 | h1610
                    · linarith only [h1, h1602, h1610, h3, hc34, hlam, hphi, u4elo4]
                    · linarith only [h1, h1599, h1602, h1604, h1610, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1613 | h1613
          · linarith only [h1, h1613, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1615 | h1615
            · linarith only [h1615, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1617 | h1617
              · linarith only [h0, h1563, h1617, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1619 | h1619
                · linarith only [h0, h1583, h1619, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1621 | h1621
                  · linarith only [h0, h1597, h1621, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1623 | h1623
                    · linarith only [h1, h1599, h1615, h1623, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1625 | h1625
                      · linarith only [h1613, h1623, h1625, h2, h3, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1627 | h1627
                        · linarith only [h1615, h1627, h2, h3, hlam]
                        · linarith only [h1623, h1627, h2, h3, hc13, hlam, hphi, ht34, u4elo4]

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2

end R2N4
