import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_60S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3452000 in
set_option maxHeartbeats 3452000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h892 | h892
  · rcases m.htr 0 1 4 (by decide) (by decide) with h893 | h893
    · rcases m.htr 0 1 5 (by decide) (by decide) with h894 | h894
      · rcases m.htr 0 2 3 (by decide) (by decide) with h895 | h895
        · rcases m.htr 0 2 4 (by decide) (by decide) with h896 | h896
          · rcases m.htr 0 2 5 (by decide) (by decide) with h897 | h897
            · rcases m.htr 0 3 4 (by decide) (by decide) with h898 | h898
              · rcases m.htr 0 3 5 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                        · linarith only [h0, h892, h903, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h898, h901, h903, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h896, h902, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h892, h901, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h910 | h910
                        · linarith only [h0, h892, h910, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h892, h898, h910, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h896, h909, hlam]
                    · linarith only [h0, h908, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h915 | h915
                  · linarith only [h898, h899, h915, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h917 | h917
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h918 | h918
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h919 | h919
                        · linarith only [h0, h892, h919, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h898, h899, h919, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h896, h918, hlam]
                    · linarith only [h0, h917, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
                · rcases m.htr 0 4 5 (by decide) (by decide) with h925 | h925
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h927 | h927
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h928 | h928
                        · linarith only [h892, h898, h928, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h930 | h930
                          · linarith only [h0, h893, h928, h930, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h898, h924, h926, h930, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h896, h927, hlam]
                    · linarith only [h0, h892, h926, hc13, hlam, hphi, u3elo2]
                  · linarith only [h898, h924, h925, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h936 | h936
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h937 | h937
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h938 | h938
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h939 | h939
                        · linarith only [h0, h892, h898, h939, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h941 | h941
                          · linarith only [h0, h892, h897, h924, h941, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h943 | h943
                            · linarith only [h0, h893, h943, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h0, h893, h936, h939, h943, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h896, h938, hlam]
                    · linarith only [h0, h937, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                        · linarith only [h0, h892, h950, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h952 | h952
                          · linarith only [h0, h892, h924, h936, h952, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h954 | h954
                            · linarith only [h893, h936, h954, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h956 | h956
                              · linarith only [h892, h898, h948, h956, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h958 | h958
                                · linarith only [h892, h924, h948, h958, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h960 | h960
                                  · linarith only [h0, h896, h936, h960, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h962 | h962
                                    · linarith only [h893, h936, h948, h950, h962, hc23, hlam, hphi, u3elo3]
                                    · rcases h0bigk with h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, hlam, p964_1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, h892, h948, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p964_1, u1elo1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, h893, h948, h950, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p964_1, u1elo1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, h893, h936, h948, h950, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p964_1, u1elo1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p964_1, u1elo1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        rcases p964_3 (m.d 0 1) (by simp) with h972 | h972
                                        · linarith only [h0, h972, hlam]
                                        · linarith only [h892, h972, hlam]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        rcases p964_3 (m.d 0 1) (by simp) with h975 | h975
                                        · linarith only [h0, h975, hlam]
                                        · linarith only [h893, h975, hlam]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        rcases p964_3 (m.d 0 1) (by simp) with h978 | h978
                                        · linarith only [h0, h978, hlam]
                                        · linarith only [h894, h978, hlam]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h892, hlam, p964_1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h895, hlam, p964_1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h898, hlam, p964_1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h924, hlam, p964_1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h893, hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h896, hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, h892, h893, h948, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p964_1, u1elo1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h936, hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h894, hlam, p964_0]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h897, hlam, p964_1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h892, h924, h948, hc23, hlam, hphi, p964_1, u3elo4]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [h0, h894, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p964_1, u1elo1]
                                      · have p964_0 := h964c.1
                                        have p964_1 := h964c.2.1
                                        have p964_2 := h964c.2.2.1
                                        have p964_3 := h964c.2.2.2
                                        linarith only [hlam, p964_0]
                      · linarith only [h0, h896, h949, hlam]
                    · linarith only [h0, h948, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h0, h894, h897, hlam]
          · linarith only [h0, h893, h896, hlam]
        · linarith only [h0, h892, h895, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1001 | h1001
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1002 | h1002
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1003 | h1003
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1004 | h1004
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1005 | h1005
                · linarith only [h1005, h892, h894, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1007 | h1007
                  · linarith only [h1004, h1007, h892, h894, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1009 | h1009
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1010 | h1010
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1011 | h1011
                        · linarith only [h1011, h892, h894, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h1004, h1005, h1011, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1002, h1009, h1010, h892, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1009, h892, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1016 | h1016
                · linarith only [h1004, h1016, h893, h894, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h1018, h893, h894, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1021 | h1021
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
                        · linarith only [h1004, h1022, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1024 | h1024
                          · linarith only [h0, h1016, h1024, h892, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h1020, h1022, h1024, h893, h894, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1002, h1021, hlam]
                    · linarith only [h0, h1001, h1020, h893, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1029 | h1029
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1030 | h1030
                · linarith only [h0, h1003, h1030, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1032 | h1032
                  · linarith only [h0, h1003, h1029, h1032, h892, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1034 | h1034
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1035 | h1035
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1036 | h1036
                        · linarith only [h0, h1036, h892, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1029, h1030, h1036, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1002, h1035, hlam]
                    · linarith only [h0, h1034, h892, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1041 | h1041
                · linarith only [h0, h1003, h1029, h1041, h893, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1043 | h1043
                  · linarith only [h0, h1003, h1043, h893, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1045 | h1045
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1046 | h1046
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1047 | h1047
                        · linarith only [h1029, h1047, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
                          · linarith only [h0, h1003, h1041, h1047, h1049, h893, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h1047, h1049, h893, h894, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1002, h1045, h1046, h892, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1045, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h1002, h893, hlam]
        · linarith only [h0, h1001, h892, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1056 | h1056
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1057 | h1057
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1058 | h1058
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1059 | h1059
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1060 | h1060
              · linarith only [h1060, h892, h893, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1062 | h1062
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1063 | h1063
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1064 | h1064
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1065 | h1065
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1066 | h1066
                        · linarith only [h1060, h1066, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1064, h1066, h892, h893, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1058, h1065, hlam]
                    · linarith only [h0, h1064, h892, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1062, h1063, h892, h893, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1072 | h1072
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1073 | h1073
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1074 | h1074
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1075 | h1075
                        · linarith only [h1075, h892, h893, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · linarith only [h1075, h892, h893, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1058, h1073, h1074, h892, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1073, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1056, h1072, h893, hlam]
            · linarith only [h0, h1056, h1059, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1082 | h1082
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1083 | h1083
              · linarith only [h0, h1058, h1083, h892, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1085 | h1085
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1087 | h1087
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
                      · linarith only [h0, h1058, h1088, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
                        · linarith only [h1083, h1090, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1087, h1090, h892, h893, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1087, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h0, h1058, h1085, h1086, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1095 | h1095
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1096 | h1096
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1097 | h1097
                      · linarith only [h0, h1058, h1097, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1099 | h1099
                        · linarith only [h1083, h1099, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1096, h1099, h892, h893, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1096, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h0, h1056, h1058, h1095, hlam]
            · linarith only [h0, h1056, h1082, hlam]
        · linarith only [h0, h1057, h892, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1106 | h1106
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1107 | h1107
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1108 | h1108
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1109 | h1109
              · linarith only [h1109, h892, h893, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1111 | h1111
                · linarith only [h1056, h1111, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1113 | h1113
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1115 | h1115
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1116 | h1116
                        · linarith only [h1109, h1116, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1114, h1116, h892, h893, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1107, h1114, h1115, h892, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1114, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1121 | h1121
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1122 | h1122
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1123 | h1123
                        · linarith only [h1122, h1123, h892, h893, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1123, h892, h893, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1107, h1122, hlam]
                    · linarith only [h0, h1121, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1128 | h1128
              · linarith only [h1128, h892, h893, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1130 | h1130
                · linarith only [h0, h1108, h1130, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1132 | h1132
                  · linarith only [h1107, h1108, h1132, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1134 | h1134
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1135 | h1135
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1136 | h1136
                        · linarith only [h1128, h1136, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1134, h1136, h892, h893, hc23, hlam, hphi, u3elo3]
                      · linarith only [h1107, h1108, h1130, h1135, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h1134, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1141 | h1141
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1142 | h1142
              · linarith only [h0, h1107, h1142, h892, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
                · linarith only [h1056, h1142, h1144, h892, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1146 | h1146
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1147 | h1147
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1148 | h1148
                      · linarith only [h1056, h1107, h1141, h1147, h1148, h892, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
                        · linarith only [h1142, h1150, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1147, h1150, h892, h893, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1147, h892, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1107, h1141, h1146, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1155 | h1155
              · linarith only [h0, h1107, h1155, h892, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1157 | h1157
                · linarith only [h1106, h1141, h1155, h1157, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1159 | h1159
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1160 | h1160
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1161 | h1161
                      · linarith only [h0, h1107, h1160, h1161, h892, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1163 | h1163
                        · linarith only [h1155, h1163, h892, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1160, h1163, h892, h893, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1160, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1167 | h1167
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
                      · linarith only [h0, h1107, h1167, h1168, h892, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1170 | h1170
                        · linarith only [h0, h1168, h1170, h892, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1167, h1168, h1170, h892, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1167, h892, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h1106, h892, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1175 | h1175
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1176 | h1176
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1177 | h1177
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1178 | h1178
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1179 | h1179
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1180 | h1180
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1181 | h1181
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1182 | h1182
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1183 | h1183
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1184 | h1184
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1185 | h1185
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1186 | h1186
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1187 | h1187
                            · linarith only [h1175, h1187, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h1175, h1182, h1187, h892, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1186, h892, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1175, h1180, h1185, h892, hlam]
                      · linarith only [h0, h1178, h1184, hlam]
                    · linarith only [h0, h1177, h1183, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1194 | h1194
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1195 | h1195
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1196 | h1196
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1197 | h1197
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1198 | h1198
                            · linarith only [h1175, h1182, h1198, h892, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1200 | h1200
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1201 | h1201
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                                  · linarith only [h1175, h1182, h1195, h1202, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1204 | h1204
                                    · linarith only [h1175, h1182, h1195, h1200, h1204, hlam]
                                    · rcases h0bigk with h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h0, hlam, p1206_1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h892, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h892, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1206_1, u3elo1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h892, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1206_1, u3elo1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p1206_1, u1elo1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h0, h1175, h1195, h1200, h892, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1206_1, u1elo1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        rcases p1206_3 (m.d 0 1) (by simp) with h1215 | h1215
                                        · linarith only [h0, h1215, hlam]
                                        · linarith only [h1175, h1215, hlam]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        rcases p1206_3 (m.d 0 1) (by simp) with h1218 | h1218
                                        · linarith only [h0, h1218, hlam]
                                        · linarith only [h1176, h1218, hlam]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1176, h1195, h1198, h1200, hc34, hlam, hphi, ht0b, ht45, ht5b, p1206_1, u0elo2]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1177, hlam, p1206_1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        rcases p1206_3 (m.d 0 1) (by simp) with h1224 | h1224
                                        · linarith only [h1224, h892, hlam]
                                        · linarith only [h1175, h1224, hlam]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        rcases p1206_3 (m.d 0 1) (by simp) with h1227 | h1227
                                        · linarith only [h1227, h892, hlam]
                                        · linarith only [h1176, h1227, hlam]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1175, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1178, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1180, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1182, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1176, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1179, hlam, p1206_1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h1181, hlam, p1206_0]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [h0, h1175, h1176, h1195, h1200, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1206_1, u1elo1]
                                      · have p1206_0 := h1206c.1
                                        have p1206_1 := h1206c.2.1
                                        have p1206_2 := h1206c.2.2.1
                                        have p1206_3 := h1206c.2.2.2
                                        linarith only [hlam, p1206_0]
                                · linarith only [h1181, h1201, h892, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1180, h1200, h892, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1175, h1195, h1197, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1196, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1178, h1195, hlam]
                    · linarith only [h0, h1194, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1176, h1181, h892, hlam]
              · linarith only [h1175, h1180, h892, hlam]
            · linarith only [h0, h1176, h1179, hlam]
          · linarith only [h1175, h1177, h1178, h892, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1250 | h1250
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1251 | h1251
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1252 | h1252
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1253 | h1253
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1254 | h1254
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1255 | h1255
                    · linarith only [h0, h1177, h1255, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1175, h1254, h1255, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
                    · linarith only [h0, h1177, h1258, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1175, h1258, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h0, h1176, h1177, h1253, hlam]
              · linarith only [h0, h1175, h1177, h1252, hlam]
            · linarith only [h0, h1176, h1251, hlam]
          · linarith only [h0, h1175, h1250, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1265 | h1265
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1266 | h1266
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1267 | h1267
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1268 | h1268
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1269 | h1269
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1270 | h1270
                  · linarith only [h1175, h1176, h1270, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1273 | h1273
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1274 | h1274
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1275 | h1275
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1276 | h1276
                            · linarith only [h1175, h1270, h1276, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1280 | h1280
                                  · linarith only [h1176, h1266, h1276, h1280, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1282 | h1282
                                    · linarith only [h1175, h1176, h1273, h1276, h1278, h1282, hlam]
                                    · rcases h0bigk with h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h0, hlam, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h892, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1175, h1176, h1273, h1275, h1278, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1284_1, u3elo1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1176, hlam, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p1284_1, u1elo1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h0, h1175, h1273, h1278, h892, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u1elo1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        rcases p1284_3 (m.d 0 1) (by simp) with h1293 | h1293
                                        · linarith only [h0, h1293, hlam]
                                        · linarith only [h1175, h1293, hlam]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h0, h1175, h1176, h1273, h1278, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u1elo1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1175, h1273, h1278, hc34, hlam, hphi, ht0b, ht45, ht5b, p1284_1, u0elo2]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1265, hlam, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        rcases p1284_3 (m.d 0 1) (by simp) with h1300 | h1300
                                        · linarith only [h1300, h892, hlam]
                                        · linarith only [h1175, h1300, hlam]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1175, h1176, h1273, h1278, h892, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1284_1, u3elo1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1175, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1266, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1268, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1270, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1175, h1273, h1278, hc34, hlam, hphi, ht0b, ht45, ht5b, p1284_1, u0elo4]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1267, hlam, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1269, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        rcases p1284_3 (m.d 0 1) (by simp) with h1312 | h1312
                                        · linarith only [h1176, h1312, hlam]
                                        · linarith only [h1175, h1312, hlam]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                · linarith only [h1269, h1279, h892, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1268, h1278, h892, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1269, h1275, h892, hlam]
                        · linarith only [h1274, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1266, h1273, hlam]
                    · linarith only [h0, h1175, h1272, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1322 | h1322
                  · linarith only [h1175, h1176, h1322, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1324 | h1324
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1325 | h1325
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1326 | h1326
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1327 | h1327
                          · linarith only [h1269, h1327, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1175, h1325, h1327, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1175, h1325, h1326, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1266, h1325, hlam]
                    · linarith only [h0, h1265, h1324, hlam]
              · linarith only [h1175, h1268, h892, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1334 | h1334
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1335 | h1335
                · linarith only [h1265, h1267, h1335, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1337 | h1337
                  · linarith only [h1175, h1265, h1267, h1337, h892, hc23, hlam, hphi, u3elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1339 | h1339
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1340 | h1340
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1341 | h1341
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1342 | h1342
                          · linarith only [h1175, h1335, h1340, h1342, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1175, h1340, h1342, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1175, h1340, h1341, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h1266, h1267, h1340, hc12, hc25, hlam, hphi]
                    · linarith only [h0, h1265, h1339, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1175, h1334, h892, hlam]
          · linarith only [h0, h1175, h1266, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1350 | h1350
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1351 | h1351
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1352 | h1352
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1353 | h1353
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1354 | h1354
                  · linarith only [h1175, h1176, h1354, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1356 | h1356
                    · linarith only [h1175, h1176, h1265, h1351, h1356, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1175, h1356, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h1265, h1351, h1353, hlam]
              · linarith only [h1175, h1176, h1265, h1351, h1352, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1361 | h1361
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1362 | h1362
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1363 | h1363
                  · linarith only [h0, h1175, h1351, h1363, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
                    · linarith only [h0, h1265, h1365, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1175, h1365, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1368 | h1368
                  · linarith only [h1175, h1362, h1368, h892, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1370 | h1370
                    · linarith only [h0, h1175, h1265, h1370, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1175, h1370, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h1175, h1265, h1361, hlam]
          · linarith only [h0, h1175, h1350, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1375 | h1375
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1376 | h1376
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1377 | h1377
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1378 | h1378
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1379 | h1379
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1380 | h1380
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1381 | h1381
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1382 | h1382
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1383 | h1383
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1386 | h1386
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1387 | h1387
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1388 | h1388
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1389 | h1389
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1390 | h1390
                                    · linarith only [h1376, h1387, h1390, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h1175, h1375, h1384, h1386, h1390, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h1175, h1375, h1384, h1386, h1389, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1380, h1388, hc23, hlam, hphi, u3elo0]
                              · linarith only [h1379, h1387, h892, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1175, h1381, h1386, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1175, h1384, h1385, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1379, h1384, h892, hlam]
                      · linarith only [h0, h1377, h1383, hlam]
                    · linarith only [h0, h1375, h1382, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1175, h1375, h1381, hlam]
                · linarith only [h1375, h1380, h892, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1403 | h1403
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1404 | h1404
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1405 | h1405
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1406 | h1406
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1407 | h1407
                        · linarith only [h1379, h1407, h892, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1375, h1407, h892, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h1375, h1377, h1405, h1406, h892, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h1375, h1405, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1375, h1379, h1404, h892, hlam]
                · linarith only [h1375, h1403, h892, hlam]
            · linarith only [h1375, h1376, h1378, h892, hc23, hlam, hphi, u3elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1415 | h1415
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1416 | h1416
              · linarith only [h1376, h1377, h1416, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1418 | h1418
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1419 | h1419
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1420 | h1420
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1421 | h1421
                      · linarith only [h1376, h1377, h1421, h892, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1423 | h1423
                        · linarith only [h1375, h1416, h1423, h892, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h1375, h1423, h892, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h0, h1375, h1376, h1420, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h1375, h1376, h1377, h1419, h892, hc23, hlam, hphi, u3elo1]
                · linarith only [h1375, h1418, h892, hlam]
            · linarith only [h0, h1375, h1415, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1430 | h1430
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1431 | h1431
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1432 | h1432
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1433 | h1433
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1434 | h1434
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1435 | h1435
                    · linarith only [h1175, h1376, h1430, h1435, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1375, h1435, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1175, h1375, h1434, hlam]
                · linarith only [h1375, h1433, h892, hlam]
              · linarith only [h1376, h1430, h1432, hlam]
            · linarith only [h1175, h1375, h1430, h1431, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1442 | h1442
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1443 | h1443
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1444 | h1444
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1445 | h1445
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
                    · linarith only [h1376, h1442, h1446, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h0, h1375, h1446, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h0, h1375, h1430, h1445, hlam]
                · linarith only [h0, h1375, h1430, h1443, h1444, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1451 | h1451
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1452 | h1452
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1453 | h1453
                    · linarith only [h0, h1375, h1376, h1453, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h0, h1375, h1453, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1375, h1443, h1452, h892, hlam]
                · linarith only [h0, h1375, h1376, h1451, hlam]
            · linarith only [h0, h1375, h1442, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1459 | h1459
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1460 | h1460
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1461 | h1461
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1462 | h1462
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1463 | h1463
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1464 | h1464
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1465 | h1465
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1466 | h1466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1467 | h1467
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1468 | h1468
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1469 | h1469
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1471 | h1471
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1472 | h1472
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1473 | h1473
                                    · linarith only [h1459, h1470, h1473, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h0, h1459, h1470, h1472, h1473, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1476 | h1476
                                    · linarith only [h1462, h1472, h1476, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h0bigk with h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h0, hlam, p1478_1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h892, hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1175, hlam, p1478_1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1375, hlam, p1478_1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p1478_1, u1elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h0, h1462, h1464, h1470, h1472, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1478_1, u1elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h0, h1464, h1470, h1472, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1478_1, u1elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h0, h1375, hc01, hlam, hphi, p1478_1, u1elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p1478_1, u3elo0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1459, hlam, p1478_1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1464, h1470, h1472, h892, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1478_1, u3elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1375, h892, hc01, hlam, hphi, ht12, ht23, p1478_1, u3elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1175, h1467, hc01, hlam, hphi, ht12, ht23, p1478_1, u3elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1460, hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1462, hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1175, h1375, h1467, hc01, hlam, hphi, ht12, ht23, p1478_1, u3elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1375, h1467, h1469, hc01, hlam, hphi, ht12, ht23, p1478_1, u3elo1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1461, hlam, p1478_1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1463, hlam, p1478_0]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [h1464, hlam, p1478_1]
                                      · have p1478_0 := h1478c.1
                                        have p1478_1 := h1478c.2.1
                                        have p1478_2 := h1478c.2.2.1
                                        have p1478_3 := h1478c.2.2.2
                                        linarith only [hlam, p1478_0]
                                · linarith only [h1463, h1471, h892, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1462, h1470, h892, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1175, h1464, h1469, hlam]
                          · linarith only [h1463, h1468, h892, hlam]
                        · linarith only [h1462, h1467, h892, hlam]
                      · linarith only [h0, h1460, h1466, hlam]
                    · linarith only [h0, h1465, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1511 | h1511
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1512 | h1512
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1513 | h1513
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1514 | h1514
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1515 | h1515
                            · linarith only [h1175, h1464, h1511, h1513, h1515, hc01, hlam, hphi, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1518 | h1518
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                                  · linarith only [h1175, h1460, h1515, h1519, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1521 | h1521
                                    · linarith only [h0, h1459, h1517, h1521, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                    · rcases h0bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h892, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1175, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1375, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p1523_1, u1elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, h892, hc01, hlam, hphi, p1523_1, u1elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, h1175, hc01, hlam, hphi, p1523_1, u1elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, h1175, h1464, hc01, hlam, hphi, p1523_1, u1elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p1523_1, u3elo0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1459, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1175, h892, hc01, hlam, hphi, ht12, ht23, p1523_1, u3elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1175, h1464, h892, hc01, hlam, hphi, ht12, ht23, p1523_1, u3elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1175, hc01, hlam, hphi, p1523_1, u1elo3]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1460, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1462, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1464, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1375, h1514, hc01, hlam, hphi, ht12, ht23, p1523_1, u3elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1461, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1463, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1175, h1375, h1514, hc01, hlam, hphi, ht12, ht23, p1523_1, u3elo1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                · linarith only [h1463, h1518, h892, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1462, h1517, h892, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1463, h1514, h892, hlam]
                        · linarith only [h1513, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1460, h1463, h1464, h1512, hc01, hlam, hphi, ht12, ht23, u3elo0]
                    · linarith only [h0, h1511, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1555 | h1555
                  · linarith only [h1462, h1463, h1555, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1557 | h1557
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1558 | h1558
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1559 | h1559
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1560 | h1560
                          · linarith only [h1463, h1560, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1560, h892, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1462, h1559, h892, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1460, h1558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1459, h1463, h1557, hc02, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1566 | h1566
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1567 | h1567
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1568 | h1568
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1569 | h1569
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1570 | h1570
                        · linarith only [h1462, h1570, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1570, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1460, h1568, h1569, h892, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1568, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1462, h1566, h1567, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1576 | h1576
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1577 | h1577
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1578 | h1578
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1579 | h1579
                        · linarith only [h1462, h1577, h1579, h892, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1579, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1460, h1578, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1577, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1584 | h1584
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1585 | h1585
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                        · linarith only [h1462, h1584, h1586, h892, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1586, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1460, h1585, hlam]
                    · linarith only [h0, h1459, h1584, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1591 | h1591
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1592 | h1592
                · linarith only [h1459, h1461, h1592, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1594 | h1594
                  · linarith only [h1459, h1461, h1591, h1592, h1594, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1596 | h1596
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1597 | h1597
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1598 | h1598
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1599 | h1599
                          · linarith only [h1592, h1599, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1599, h892, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1591, h1598, h892, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1460, h1461, h1597, hc12, hc25, hlam, hphi]
                    · linarith only [h0, h1596, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1605 | h1605
                · linarith only [h1460, h1461, h1591, h1605, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1607 | h1607
                  · linarith only [h1460, h1461, h1607, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1609 | h1609
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1610 | h1610
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1611 | h1611
                        · linarith only [h1591, h1611, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1611, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1460, h1461, h1605, h1610, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h1459, h1609, hc01, hlam, hphi, ht12, ht23, u3elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1616 | h1616
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1617 | h1617
              · linarith only [h1459, h1460, h1617, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1619 | h1619
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1620 | h1620
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1621 | h1621
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1622 | h1622
                      · linarith only [h1459, h1460, h1622, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1624 | h1624
                        · linarith only [h1375, h1617, h1619, h1624, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1624, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1459, h1621, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1460, h1616, h1620, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1629 | h1629
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1630 | h1630
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1631 | h1631
                      · linarith only [h1459, h1460, h1631, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1633 | h1633
                        · linarith only [h1617, h1630, h1633, h892, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1633, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1459, h1630, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1460, h1616, h1629, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1638 | h1638
              · linarith only [h1459, h1460, h1638, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1640 | h1640
                · linarith only [h1459, h1616, h1638, h1640, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1643 | h1643
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1644 | h1644
                      · linarith only [h1459, h1460, h1644, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1646 | h1646
                        · linarith only [h1638, h1643, h1646, h892, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1646, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1459, h1616, h1643, hc12, hc25, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1650 | h1650
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1651 | h1651
                      · linarith only [h1459, h1460, h1651, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1653 | h1653
                        · linarith only [h1638, h1653, h892, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1653, h892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1459, h1616, h1650, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1657 | h1657
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1658 | h1658
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1659 | h1659
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1660 | h1660
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1662 | h1662
                    · linarith only [h1459, h1657, h1662, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1662, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1665 | h1665
                    · linarith only [h1459, h1657, h1665, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1665, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1459, h1658, h1660, hlam]
              · linarith only [h1459, h1657, h1659, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1670 | h1670
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1671 | h1671
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1672 | h1672
                  · linarith only [h1657, h1658, h1672, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1674 | h1674
                    · linarith only [h1459, h1657, h1674, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1674, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1677 | h1677
                  · linarith only [h1459, h1657, h1671, h1677, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1679 | h1679
                    · linarith only [h1459, h1657, h1679, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1679, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1459, h1657, h1670, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1683 | h1683
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1684 | h1684
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1685 | h1685
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1686 | h1686
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1687 | h1687
                    · linarith only [h1459, h1683, h1687, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h0, h1687, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1657, h1683, h1686, hlam]
                · linarith only [h1657, h1683, h1684, h1685, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1692 | h1692
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1693 | h1693
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1694 | h1694
                    · linarith only [h1459, h1683, h1694, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h0, h1694, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1459, h1683, h1684, h1693, hlam]
                · linarith only [h1459, h1683, h1692, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1699 | h1699
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1700 | h1700
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1701 | h1701
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1702 | h1702
                    · linarith only [h0, h1459, h1702, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1702, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1705 | h1705
                    · linarith only [h0, h1459, h1705, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1705, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1708 | h1708
                  · linarith only [h1699, h1700, h1708, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1710 | h1710
                    · linarith only [h0, h1459, h1710, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1710, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1713 | h1713
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1714 | h1714
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1715 | h1715
                    · linarith only [h0, h1459, h1715, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1715, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1699, h1713, h1714, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1719 | h1719
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1720 | h1720
                    · linarith only [h0, h1459, h1720, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1720, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
                    · linarith only [h0, h1459, h1723, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1723, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3452000 in
set_option maxHeartbeats 3452000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_0_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_0_L_I_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
