import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_60S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3480000 in
set_option maxHeartbeats 3480000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h933 | h933
  · rcases m.htr 0 1 4 (by decide) (by decide) with h934 | h934
    · rcases m.htr 0 1 5 (by decide) (by decide) with h935 | h935
      · rcases m.htr 0 2 3 (by decide) (by decide) with h936 | h936
        · rcases m.htr 0 2 4 (by decide) (by decide) with h937 | h937
          · rcases m.htr 0 2 5 (by decide) (by decide) with h938 | h938
            · rcases m.htr 0 3 4 (by decide) (by decide) with h939 | h939
              · rcases m.htr 0 3 5 (by decide) (by decide) with h940 | h940
                · rcases m.htr 0 4 5 (by decide) (by decide) with h941 | h941
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h942 | h942
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h943 | h943
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h944 | h944
                        · linarith only [h0, h933, h944, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h933, h939, h944, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h943, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h936, h942, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h951 | h951
                        · linarith only [h0, h933, h951, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h933, h939, h951, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h950, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h933, h936, h939, h949, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h956 | h956
                  · linarith only [h939, h940, h956, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                        · linarith only [h0, h933, h960, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h939, h940, h958, h960, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h933, h958, h959, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h936, h958, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h965 | h965
                · rcases m.htr 0 4 5 (by decide) (by decide) with h966 | h966
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h967 | h967
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h968 | h968
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
                        · linarith only [h0, h933, h969, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h971 | h971
                          · linarith only [h0, h934, h969, h971, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h939, h965, h967, h971, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h968, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h936, h967, hlam]
                  · linarith only [h939, h965, h966, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h977 | h977
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                        · linarith only [h0, h933, h980, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                          · linarith only [h0, h934, h980, h982, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                            · linarith only [h0, h934, h984, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h0, h934, h977, h978, h980, h984, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h979, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h936, h978, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h989 | h989
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h990 | h990
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h991 | h991
                        · linarith only [h0, h933, h991, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h993 | h993
                          · linarith only [h965, h991, h993, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h995 | h995
                            · linarith only [h0, h934, h977, h995, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
                              · linarith only [h933, h939, h989, h997, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h999 | h999
                                · linarith only [h933, h939, h977, h989, h999, hc23, hlam, hphi, ht34, u4elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1001 | h1001
                                  · linarith only [h1001, h933, h939, h977, h989, hc23, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h1001, h933, h939, h989, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h990, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h936, h989, hlam]
            · linarith only [h0, h935, h938, hlam]
          · linarith only [h0, h933, h937, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h933, h936, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1009 | h1009
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1010 | h1010
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1011 | h1011
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1012 | h1012
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1013 | h1013
                · linarith only [h1013, h933, h935, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1015 | h1015
                  · linarith only [h1015, h934, h935, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1017 | h1017
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1018 | h1018
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1019 | h1019
                        · linarith only [h0, h1019, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h1012, h1019, h933, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h1018, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1009, h1017, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1024 | h1024
                · linarith only [h1012, h1024, h933, h935, hc13, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1026 | h1026
                  · linarith only [h1026, h934, h935, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1029 | h1029
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1030 | h1030
                        · linarith only [h0, h1030, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1032 | h1032
                          · linarith only [h0, h1024, h1030, h1032, h934, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1034 | h1034
                            · linarith only [h0, h1026, h1034, h934, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h1034, h934, h935, hc14, hlam, hphi, u4elo4]
                      · linarith only [h0, h1028, h1029, h933, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1009, h1028, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1039 | h1039
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1040 | h1040
                · linarith only [h0, h1011, h1040, h933, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1042 | h1042
                  · linarith only [h0, h1011, h1039, h1042, h933, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1044 | h1044
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1045 | h1045
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1046 | h1046
                        · linarith only [h0, h1046, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h1039, h1046, h933, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h1045, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1009, h1044, h933, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1051 | h1051
                · linarith only [h0, h1011, h1051, h933, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1053 | h1053
                  · linarith only [h0, h1011, h1053, h934, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1055 | h1055
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1056 | h1056
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1057 | h1057
                        · linarith only [h0, h1057, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1059 | h1059
                          · linarith only [h0, h1011, h1051, h1059, h933, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1061 | h1061
                            · linarith only [h0, h1039, h1053, h1061, h934, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h1055, h1061, h933, h935, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1055, h1056, h933, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1009, h1055, hlam]
          · linarith only [h0, h1010, h933, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h1009, h933, hlam]
    · linarith only [h933, h934, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1069 | h1069
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1070 | h1070
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1071 | h1071
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1072 | h1072
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1073 | h1073
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1074 | h1074
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1076 | h1076
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1077 | h1077
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1078 | h1078
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1079 | h1079
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1080 | h1080
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1081 | h1081
                            · linarith only [h1069, h1077, h1081, h933, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h1076, h1081, hc14, hlam, hphi, u4elo0]
                          · linarith only [h1069, h1071, h1075, h1078, h1080, h933, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1069, h1078, h1079, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1069, h1078, hc14, hlam, hphi, u4elo2]
                    · linarith only [h0, h1071, h1077, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1089 | h1089
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1091 | h1091
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1092 | h1092
                            · linarith only [h1069, h1076, h1092, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1094 | h1094
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1095 | h1095
                                · linarith only [h1069, h1076, h1089, h1095, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1097 | h1097
                                  · linarith only [h1069, h1076, h1089, h1094, h1097, hlam]
                                  · rcases h0bigk with h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h0, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h933, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1088, h933, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1, u1elo1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1088, h933, hc05, hlam, hphi, ht01, ht0b, ht5b, p1099_1, u1elo1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p1099_1, u1elo1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h0, h1069, h1089, h1094, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1, u1elo1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      rcases p1099_3 (m.d 0 1) (by simp) with h1108 | h1108
                                      · linarith only [h0, h1108, hlam]
                                      · linarith only [h1069, h1108, hlam]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      rcases p1099_3 (m.d 0 1) (by simp) with h1111 | h1111
                                      · linarith only [h0, h1111, hlam]
                                      · linarith only [h1070, h1111, hlam]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1070, h1089, h1092, h1094, hc34, hlam, hphi, ht0b, ht45, ht5b, p1099_1, u0elo2]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1071, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      rcases p1099_3 (m.d 0 1) (by simp) with h1117 | h1117
                                      · linarith only [h1117, h933, hlam]
                                      · linarith only [h1069, h1117, hlam]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      rcases p1099_3 (m.d 0 1) (by simp) with h1120 | h1120
                                      · linarith only [h1120, h933, hlam]
                                      · linarith only [h1070, h1120, hlam]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1069, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1072, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1074, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1076, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1070, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1073, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1075, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h0, h1069, h1070, h1089, h1094, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1, u1elo1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                              · linarith only [h1074, h1076, h1094, hc23, hlam, hphi, ht34, u4elo4]
                          · linarith only [h1075, h1091, h933, hlam]
                        · linarith only [h1069, h1089, h1090, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h1088, h1089, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1071, h1088, hlam]
                · linarith only [h1070, h1075, h933, hlam]
              · linarith only [h1069, h1074, h933, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h1070, h1073, hlam]
          · linarith only [h1069, h1071, h1072, h933, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1142 | h1142
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1143 | h1143
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1144 | h1144
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1145 | h1145
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1146 | h1146
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1147 | h1147
                    · linarith only [h1071, h1142, h1147, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1149 | h1149
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1151 | h1151
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1152 | h1152
                            · linarith only [h0, h1069, h1147, h1152, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h1146, h1150, h1152, hc34, hlam, hphi, u4elo0]
                          · linarith only [h0, h1145, h1147, h1151, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1069, h1149, h1150, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1149, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1158 | h1158
                    · linarith only [h0, h1069, h1071, h1158, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1160 | h1160
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1161 | h1161
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1162 | h1162
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1163 | h1163
                            · linarith only [h1069, h1146, h1163, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1165 | h1165
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1166 | h1166
                                · linarith only [h1069, h1146, h1160, h1166, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1168 | h1168
                                  · linarith only [h1069, h1146, h1160, h1165, h1168, hlam]
                                  · rcases h0bigk with h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h0, hlam, p1170_1]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h933, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h0, h1158, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1170_1]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h0, h1158, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1170_1]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1071, h933, hc01, hlam, hphi, p1170_1, u1elo2]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1071, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      rcases p1170_3 (m.d 0 1) (by simp) with h1179 | h1179
                                      · linarith only [h0, h1179, hlam]
                                      · linarith only [h1069, h1179, hlam]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      rcases p1170_3 (m.d 0 1) (by simp) with h1182 | h1182
                                      · linarith only [h0, h1182, hlam]
                                      · linarith only [h1070, h1182, hlam]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1070, h1160, h1163, h1165, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1170_1, u1elo2]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h0, h1070, h1160, h1163, h1165, h933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1170_1, u1elo2]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      rcases p1170_3 (m.d 0 1) (by simp) with h1188 | h1188
                                      · linarith only [h1188, h933, hlam]
                                      · linarith only [h1069, h1188, hlam]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      rcases p1170_3 (m.d 0 1) (by simp) with h1191 | h1191
                                      · linarith only [h1191, h933, hlam]
                                      · linarith only [h1070, h1191, hlam]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1069, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1142, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1144, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1146, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1070, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1143, hlam, p1170_1]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h1145, hlam, p1170_0]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [h0, h1069, h1070, h1158, h1160, h1165, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1170_1]
                                    · have p1170_0 := h1170c.1
                                      have p1170_1 := h1170c.2.1
                                      have p1170_2 := h1170c.2.2.1
                                      have p1170_3 := h1170c.2.2.2
                                      linarith only [hlam, p1170_0]
                              · linarith only [h0, h1158, h1165, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1145, h1162, h933, hlam]
                        · linarith only [h1069, h1160, h1161, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1069, h1160, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h1070, h1071, h1145, hlam]
              · linarith only [h0, h1069, h1071, h1144, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h1070, h1143, hlam]
          · linarith only [h0, h1069, h1142, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1212 | h1212
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1213 | h1213
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1214 | h1214
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1216 | h1216
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1217 | h1217
                  · linarith only [h1069, h1070, h1217, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1219 | h1219
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1220 | h1220
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1221 | h1221
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1222 | h1222
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1223 | h1223
                            · linarith only [h1069, h1217, h1223, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1069, h1070, h1220, h1223, hc24, hlam, hphi, u4elo4]
                          · linarith only [h0, h1069, h1212, h1216, h1220, h1222, h933, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1069, h1220, h1221, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1069, h1220, hc14, hlam, hphi, u4elo2]
                    · linarith only [h0, h1212, h1219, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1230 | h1230
                  · linarith only [h1069, h1216, h1230, h933, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1232 | h1232
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1233 | h1233
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1234 | h1234
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
                          · linarith only [h1069, h1216, h1232, h1233, h1235, h933, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                            · linarith only [h1069, h1230, h1237, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1069, h1233, h1235, h1237, h933, hc24, hlam, hphi, u4elo4]
                        · linarith only [h1069, h1233, h1234, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1233, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1212, h1232, hlam]
              · linarith only [h1069, h1215, h933, hc14, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1244 | h1244
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1245 | h1245
                · linarith only [h1212, h1214, h1245, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1247 | h1247
                  · linarith only [h0, h1069, h1214, h1247, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1250 | h1250
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1251 | h1251
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1252 | h1252
                          · linarith only [h1245, h1249, h1252, h933, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1254 | h1254
                            · linarith only [h1069, h1212, h1214, h1247, h1254, h933, hlam]
                            · linarith only [h1069, h1070, h1250, h1254, hc24, hlam, hphi, u4elo4]
                        · linarith only [h1069, h1250, h1251, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1250, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1069, h1212, h1249, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h1069, h1244, h933, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h1069, h1213, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1262 | h1262
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1263 | h1263
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1264 | h1264
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1265 | h1265
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1266 | h1266
                  · linarith only [h1069, h1070, h1266, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1268 | h1268
                    · linarith only [h1069, h1070, h1212, h1263, h1268, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1270 | h1270
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1271 | h1271
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1272 | h1272
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1273 | h1273
                            · linarith only [h1069, h1266, h1273, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1069, h1070, h1273, hc14, hlam, hphi, u4elo4]
                          · linarith only [h1265, h1272, h933, hlam]
                        · linarith only [h0, h1069, h1268, h1270, h1271, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1270, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h1212, h1263, h1265, hlam]
              · linarith only [h0, h1069, h1212, h1264, hc14, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1281 | h1281
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1282 | h1282
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1283 | h1283
                  · linarith only [h0, h1069, h1263, h1283, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
                    · linarith only [h0, h1069, h1212, h1285, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1287 | h1287
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1289 | h1289
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1290 | h1290
                            · linarith only [h1069, h1283, h1290, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1069, h1070, h1290, hc14, hlam, hphi, u4elo4]
                          · linarith only [h1282, h1289, h933, hlam]
                        · linarith only [h1069, h1287, h1288, h933, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1287, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1296 | h1296
                  · linarith only [h1069, h1282, h1296, h933, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
                    · linarith only [h1212, h1262, h1298, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1300 | h1300
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
                          · linarith only [h0, h1069, h1212, h1282, h1300, h1302, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1304 | h1304
                            · linarith only [h0, h1069, h1212, h1282, h1296, h1304, hlam]
                            · linarith only [h1069, h1300, h1302, h1304, h933, hc24, hlam, hphi, u4elo4]
                        · linarith only [h0, h1069, h1298, h1300, h1301, hc24, hlam, hphi, u4elo3]
                      · linarith only [h0, h1300, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1069, h1212, h1281, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h1069, h1262, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1311 | h1311
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1312 | h1312
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1313 | h1313
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1314 | h1314
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1315 | h1315
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1316 | h1316
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1317 | h1317
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1318 | h1318
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1319 | h1319
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1320 | h1320
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1321 | h1321
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1322 | h1322
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1323 | h1323
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1324 | h1324
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1325 | h1325
                                  · linarith only [h1312, h1323, h1325, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1317, h1325, hc34, hlam, hphi, u4elo0]
                                · linarith only [h1069, h1311, h1322, h1324, hc24, hlam, hphi, u4elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1329 | h1329
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1330 | h1330
                                  · rcases h0bigk with h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h933, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1069, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1069, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1331_1, u4elo1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p1331_1, u1elo1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, h1069, h1311, h1315, h1321, h1323, h1330, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p1331_1, u1elo1, u4elo1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, h1069, h1311, h1321, h1330, hc45, hlam, hphi, ht01, ht0b, ht5b, p1331_1, u1elo1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      rcases p1331_3 (m.d 0 1) (by simp) with h1341 | h1341
                                      · linarith only [h0, h1341, hlam]
                                      · linarith only [h1311, h1341, hlam]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1311, h1321, h1330, hc45, hlam, hphi, ht0b, ht5b, p1331_1, u0elo2]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1312, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, h1069, h1311, h1312, h1315, h1321, h1323, h1330, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p1331_1, u1elo1, u4elo1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      rcases p1331_3 (m.d 0 1) (by simp) with h1348 | h1348
                                      · linarith only [h1348, h933, hlam]
                                      · linarith only [h1311, h1348, hlam]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1311, h1321, h1330, hc45, hlam, hphi, ht0b, ht5b, p1331_1, u0elo3]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1313, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1315, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      rcases p1331_3 (m.d 0 1) (by simp) with h1355 | h1355
                                      · linarith only [h1069, h1355, hlam]
                                      · linarith only [h1311, h1355, hlam]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1311, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1314, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1316, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1317, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                  · linarith only [h1323, h1330, hc23, hlam, hphi, ht34, u4elo4]
                                · linarith only [h0, h1311, h1322, h1329, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h1069, h1311, h1321, h1322, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h1316, h1321, h933, hlam]
                        · linarith only [h1315, h1320, h933, hlam]
                      · linarith only [h0, h1319, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1312, h1318, hlam]
                  · linarith only [h1069, h1311, h1317, hlam]
                · linarith only [h1069, h1311, h1315, h1316, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1372 | h1372
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1373 | h1373
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1374 | h1374
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1375 | h1375
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1376 | h1376
                        · linarith only [h1315, h1374, h1376, h933, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1311, h1376, h933, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h0, h1311, h1313, h1375, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h1312, h1374, hlam]
                  · linarith only [h1311, h1315, h1373, h933, hlam]
                · linarith only [h1311, h1372, h933, hlam]
            · linarith only [h0, h1311, h1314, hlam]
          · linarith only [h1312, h1313, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1385 | h1385
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1386 | h1386
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1387 | h1387
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1388 | h1388
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
                    · linarith only [h1312, h1385, h1390, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1392 | h1392
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1393 | h1393
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1394 | h1394
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1395 | h1395
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1396 | h1396
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1397 | h1397
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1398 | h1398
                                  · rcases h0bigk with h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h0, hlam, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h933, hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1069, hlam, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h0, h1386, h1390, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h0, h1390, hc01, hc23, hlam, hphi, ht12, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1312, hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h0, h1069, h1311, h1390, h1394, h1398, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      rcases p1399_3 (m.d 0 1) (by simp) with h1409 | h1409
                                      · linarith only [h0, h1409, hlam]
                                      · linarith only [h1311, h1409, hlam]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1311, h1394, h1398, hc45, hlam, hphi, ht0b, ht5b, p1399_1, u0elo2]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h0, h1311, h1394, h1398, h933, hc45, hlam, hphi, ht01, ht0b, ht5b, p1399_1, u1elo2]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1069, h1311, h1394, h1398, h933, hc45, hlam, hphi, ht01, ht0b, ht5b, p1399_1, u1elo2]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      rcases p1399_3 (m.d 0 1) (by simp) with h1416 | h1416
                                      · linarith only [h1416, h933, hlam]
                                      · linarith only [h1311, h1416, hlam]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1311, h1394, h1398, hc45, hlam, hphi, ht0b, ht5b, p1399_1, u0elo3]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1385, hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1387, hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      rcases p1399_3 (m.d 0 1) (by simp) with h1423 | h1423
                                      · linarith only [h1069, h1423, hlam]
                                      · linarith only [h1311, h1423, hlam]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1311, hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1386, hlam, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1388, hlam, p1399_0]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [h1389, hlam, p1399_1]
                                    · have p1399_0 := h1399c.1
                                      have p1399_1 := h1399c.2.1
                                      have p1399_2 := h1399c.2.2.1
                                      have p1399_3 := h1399c.2.2.2
                                      linarith only [hlam, p1399_0]
                                  · linarith only [h1069, h1311, h1386, h1397, h1398, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1069, h1311, h1395, h1397, hc24, hlam, hphi, u4elo1]
                              · linarith only [h1390, h1396, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h1069, h1395, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h1388, h1394, h933, hlam]
                        · linarith only [h1387, h1393, h933, hlam]
                      · linarith only [h0, h1311, h1392, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                  · linarith only [h1069, h1311, h1389, hlam]
                · linarith only [h1311, h1388, h933, hlam]
              · linarith only [h1312, h1385, h1387, hc24, hlam, hphi, u4elo3]
            · linarith only [h1069, h1311, h1385, h1386, hc24, hlam, hphi, u4elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1442 | h1442
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1443 | h1443
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1444 | h1444
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1445 | h1445
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
                    · linarith only [h0, h1312, h1446, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1448 | h1448
                      · linarith only [h0, h1311, h1385, h1448, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h1311, h1448, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                  · linarith only [h0, h1311, h1385, h1445, hlam]
                · linarith only [h1311, h1444, h933, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1453 | h1453
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1454 | h1454
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1455 | h1455
                    · linarith only [h0, h1311, h1312, h1455, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
                      · linarith only [h0, h1311, h1385, h1455, h1457, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1311, h1457, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                  · linarith only [h1069, h1311, h1454, hlam]
                · linarith only [h0, h1311, h1312, h1453, hlam]
            · linarith only [h0, h1311, h1442, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1463 | h1463
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1464 | h1464
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1465 | h1465
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1466 | h1466
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1467 | h1467
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1470 | h1470
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1472 | h1472
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1473 | h1473
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1474 | h1474
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1475 | h1475
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1476 | h1476
                                  · linarith only [h1463, h1474, h1476, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1464, h1475, h1476, hc34, hlam, hphi, u4elo0]
                                · linarith only [h1069, h1468, h1475, hc24, hlam, hphi, u4elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1480 | h1480
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1481 | h1481
                                  · rcases h0bigk with h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, hlam, p1482_1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h933, hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1069, hlam, p1482_1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1311, hlam, p1482_1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p1482_1, u1elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, h1466, h1474, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1482_1, u1elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, h1069, hc01, hlam, hphi, p1482_1, u1elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, h1311, hc01, hlam, hphi, p1482_1, u1elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h933, hc01, hlam, hphi, p1482_1, u1elo2]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1463, hlam, p1482_1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, h1463, h1464, h1480, hc45, hlam, hphi, ht01, ht0b, ht5b, p1482_1, u1elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, h1311, h1463, hc01, hlam, hphi, p1482_1, u1elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1482_1, u4elo0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1464, hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1466, hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h0, h1069, h1311, h1463, h1466, h1474, hc01, hc23, hlam, hphi, ht34, p1482_1, u1elo1, u4elo1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1311, hc01, hlam, hphi, p1482_1, u1elo4]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1465, hlam, p1482_1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1467, hlam, p1482_0]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [h1468, hlam, p1482_1]
                                    · have p1482_0 := h1482c.1
                                      have p1482_1 := h1482c.2.1
                                      have p1482_2 := h1482c.2.2.1
                                      have p1482_3 := h1482c.2.2.2
                                      linarith only [hlam, p1482_0]
                                  · linarith only [h1474, h1481, hc23, hlam, hphi, ht34, u4elo4]
                                · linarith only [h1069, h1468, h1480, hc24, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1468, h1473, hlam]
                          · linarith only [h0, h1463, h1467, h1472, h933, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1466, h1471, h933, hlam]
                      · linarith only [h0, h1463, h1466, h1470, hc34, hlam, hphi, u4elo2]
                    · linarith only [h0, h1463, h1469, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1515 | h1515
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1516 | h1516
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1517 | h1517
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1518 | h1518
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1519 | h1519
                            · linarith only [h1468, h1519, hc04, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1519, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h1467, h1518, h933, hlam]
                        · linarith only [h1466, h1517, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                      · linarith only [h0, h1463, h1516, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1463, h1515, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
                  · linarith only [h1466, h1467, h1526, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1529 | h1529
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1530 | h1530
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1531 | h1531
                          · linarith only [h1466, h1467, h1531, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1533 | h1533
                            · linarith only [h1526, h1533, hc04, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1533, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1466, h1530, h933, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1463, h1529, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1463, h1528, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1539 | h1539
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1540 | h1540
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1541 | h1541
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1542 | h1542
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1543 | h1543
                        · linarith only [h1466, h1539, h1543, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h1543, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1464, h1542, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1463, h1466, h1541, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1466, h1539, h1540, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1549 | h1549
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1550 | h1550
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1551 | h1551
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1552 | h1552
                        · linarith only [h1466, h1550, h1552, h933, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1552, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1551, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1463, h1550, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1557 | h1557
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1558 | h1558
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1559 | h1559
                        · linarith only [h1466, h1559, h933, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1559, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1464, h1549, h1558, hc02, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h1463, h1557, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1564 | h1564
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1565 | h1565
                · linarith only [h1463, h1465, h1565, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1567 | h1567
                  · linarith only [h1464, h1465, h1567, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1569 | h1569
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1570 | h1570
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1571 | h1571
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1572 | h1572
                          · linarith only [h1565, h1569, h1572, h933, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1574 | h1574
                            · linarith only [h1567, h1574, hc04, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1574, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1564, h1571, h933, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1464, h1465, h1570, hc12, hc25, hlam, hphi]
                    · linarith only [h0, h1463, h1569, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1580 | h1580
                · linarith only [h1463, h1465, h1580, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1582 | h1582
                  · linarith only [h1464, h1465, h1582, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1584 | h1584
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1585 | h1585
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                        · linarith only [h1564, h1586, h933, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1586, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1464, h1585, hlam]
                    · linarith only [h0, h1463, h1584, h933, hc01, hlam, hphi, u1elo2]
          · linarith only [h1463, h1464, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1592 | h1592
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1593 | h1593
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1594 | h1594
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1595 | h1595
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1596 | h1596
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1597 | h1597
                    · linarith only [h1463, h1592, h1597, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1599 | h1599
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1600 | h1600
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1601 | h1601
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1602 | h1602
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1603 | h1603
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1604 | h1604
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1605 | h1605
                                  · rcases h0bigk with h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h0, hlam, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h933, hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1069, hlam, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1311, hlam, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p1606_1, u1elo1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1463, hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h0, h1592, h1597, h1603, h1605, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h0, h1311, h1597, hc01, hc23, hlam, hphi, ht12, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h933, hc01, hlam, hphi, p1606_1, u1elo2]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h0, h933, hc01, hlam, hphi, p1606_1, u1elo2]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1592, h1603, h1605, h933, hc45, hlam, hphi, ht01, ht0b, ht5b, p1606_1, u1elo2]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1311, h933, hc01, hlam, hphi, p1606_1, u1elo2]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1606_1, u4elo0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1592, hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1594, hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1069, h1311, hc01, hlam, hphi, ht12, ht23, ht34, p1606_1, u4elo1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1311, hc01, hlam, hphi, p1606_1, u1elo4]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1593, hlam, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1595, hlam, p1606_0]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [h1596, hlam, p1606_1]
                                    · have p1606_0 := h1606c.1
                                      have p1606_1 := h1606c.2.1
                                      have p1606_2 := h1606c.2.2.1
                                      have p1606_3 := h1606c.2.2.2
                                      linarith only [hlam, p1606_0]
                                  · linarith only [h1069, h1596, h1605, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1069, h1596, h1603, h1604, hc34, hlam, hphi, u4elo1]
                              · linarith only [h0, h1597, h1603, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h1069, h1596, h1602, hlam]
                          · linarith only [h1595, h1601, h933, hlam]
                        · linarith only [h1594, h1600, h933, hlam]
                      · linarith only [h0, h1599, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1639 | h1639
                    · linarith only [h1463, h1592, h1639, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1641 | h1641
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1642 | h1642
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1643 | h1643
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1644 | h1644
                            · linarith only [h1594, h1596, h1644, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1644, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h0, h1593, h1595, h1639, h1643, h933, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1642, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1592, h1641, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1463, h1593, h1595, hlam]
              · linarith only [h1463, h1592, h1594, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1652 | h1652
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1653 | h1653
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1654 | h1654
                  · linarith only [h1592, h1593, h1654, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1656 | h1656
                    · linarith only [h1463, h1592, h1656, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1658 | h1658
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1659 | h1659
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1660 | h1660
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1661 | h1661
                            · linarith only [h1654, h1661, hc04, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1661, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h1653, h1660, h933, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1652, h1659, h933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                      · linarith only [h1592, h1593, h1658, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1667 | h1667
                  · linarith only [h1463, h1592, h1653, h1667, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1669 | h1669
                    · linarith only [h1463, h1592, h1669, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1671 | h1671
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1672 | h1672
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1673 | h1673
                          · linarith only [h1652, h1653, h1673, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1675 | h1675
                            · linarith only [h1592, h1593, h1667, h1675, hc24, hlam, hphi, u4elo1]
                            · linarith only [h1069, h1675, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h1669, h1672, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1592, h1671, hlam]
              · linarith only [h1463, h1592, h1652, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1681 | h1681
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1682 | h1682
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1683 | h1683
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1684 | h1684
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1685 | h1685
                    · linarith only [h1463, h1681, h1685, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1687 | h1687
                      · linarith only [h1592, h1681, h1687, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h1687, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h1592, h1681, h1684, hlam]
                · linarith only [h1592, h1681, h1682, h1683, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1692 | h1692
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1693 | h1693
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1694 | h1694
                    · linarith only [h1463, h1681, h1694, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1696 | h1696
                      · linarith only [h1592, h1681, h1696, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h1696, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h1463, h1681, h1682, h1693, hlam]
                · linarith only [h1463, h1681, h1692, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1701 | h1701
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1702 | h1702
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1704 | h1704
                    · linarith only [h0, h1463, h1704, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1706 | h1706
                      · linarith only [h0, h1592, h1704, h1706, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1706, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
                    · linarith only [h0, h1463, h1709, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1711 | h1711
                      · linarith only [h0, h1592, h1711, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1711, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1714 | h1714
                  · linarith only [h1701, h1702, h1714, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1716 | h1716
                    · linarith only [h0, h1463, h1716, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1718 | h1718
                      · linarith only [h0, h1592, h1716, h1718, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1718, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1721 | h1721
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1722 | h1722
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
                    · linarith only [h0, h1463, h1723, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1725 | h1725
                      · linarith only [h0, h1592, h1723, h1725, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1725, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h1701, h1721, h1722, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1729 | h1729
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1730 | h1730
                    · linarith only [h0, h1463, h1730, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1732 | h1732
                      · linarith only [h0, h1592, h1732, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1732, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1735 | h1735
                    · linarith only [h0, h1463, h1735, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1737 | h1737
                      · linarith only [h0, h1592, h1735, h1737, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1737, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 3480000 in
set_option maxHeartbeats 3480000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_0_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_0_x1 m hb0 hb1 hb3 hb4 h0

set_option maxHeartbeats 3472000 in
set_option maxHeartbeats 3472000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h10, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h13, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h18, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h23, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h23, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h21, h22, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h28, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h28, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h31, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h31, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                · linarith only [h35, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
                  · linarith only [h34, h35, h37, h4, h6, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                    · linarith only [h0, h39, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h39, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
                · linarith only [h34, h4, h42, h6, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h44, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h46, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h46, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
            · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
              · linarith only [h4, h5, h50, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h2, h4, h5, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h4, h5, h50, h52, h53, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                    · linarith only [h0, h59, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h49, h5, h58, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
              · linarith only [h4, h5, h63, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                · linarith only [h4, h49, h63, h65, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                    · linarith only [h0, h68, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h68, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                    · linarith only [h0, h71, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h5, h67, h71, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
          · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                    · linarith only [h0, h79, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                      · linarith only [h1, h79, h81, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h74, h81, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h4, h84, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                      · linarith only [h1, h84, h86, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h74, h86, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4, h75, h77, hlam]
              · linarith only [h4, h74, h76, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
              · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                  · linarith only [h74, h75, h93, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                    · linarith only [h0, h95, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                      · linarith only [h1, h95, h97, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h4, h74, h97, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                  · linarith only [h100, h4, h74, h92, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                    · linarith only [h0, h102, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                      · linarith only [h1, h102, h104, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h104, h4, h74, h92, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h4, h74, h91, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h108 | h108
            · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
              · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                    · linarith only [h0, h112, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                      · linarith only [h1, h108, h112, h114, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h1, h112, h116, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h108, h116, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h108, h111, h74, hlam]
                · linarith only [h108, h109, h110, h74, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
                · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                    · linarith only [h0, h123, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                      · linarith only [h1, h108, h123, h125, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h1, h123, h127, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h108, h127, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h108, h109, h122, h4, hlam]
                · linarith only [h108, h121, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
              · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                    · linarith only [h0, h135, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                      · linarith only [h0, h137, h74, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                        · linarith only [h0, h108, h139, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                          · linarith only [h1, h141, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h132, h141, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                    · linarith only [h0, h144, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                      · linarith only [h144, h146, h74, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                        · linarith only [h1, h108, h144, h148, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                          · linarith only [h1, h150, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h132, h150, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h132, h133, h153, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                    · linarith only [h0, h155, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                      · linarith only [h0, h157, h74, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                        · linarith only [h0, h108, h159, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                          · linarith only [h1, h161, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h132, h133, h161, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                    · linarith only [h0, h166, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                      · linarith only [h0, h168, h74, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                        · linarith only [h0, h108, h170, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                          · linarith only [h1, h132, h172, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                            · linarith only [h172, h174, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h164, h174, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h132, h164, h165, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                    · linarith only [h0, h179, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h0, h181, h74, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h0, h108, h183, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                          · linarith only [h132, h185, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                            · linarith only [h1, h164, h187, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                              · linarith only [h189, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h178, h189, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                    · linarith only [h0, h192, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                      · linarith only [h0, h194, h74, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                        · linarith only [h0, h108, h196, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                          · linarith only [h1, h132, h198, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                            · linarith only [h0, h164, h200, h4, hc12, hlam, hphi, ht23, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                              · linarith only [h0, h132, h178, h2, h202, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                                · linarith only [h0, h132, h204, h4, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h204, h4, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h207 | h207
        · rcases m.htr 0 2 4 (by decide) (by decide) with h208 | h208
          · rcases m.htr 0 2 5 (by decide) (by decide) with h209 | h209
            · linarith only [h0, h209, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h211 | h211
              · rcases m.htr 0 3 5 (by decide) (by decide) with h212 | h212
                · linarith only [h1, h212, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h214 | h214
                  · linarith only [h2, h214, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                    · linarith only [h0, h216, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h207, h216, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h219 | h219
                · linarith only [h0, h207, h211, h219, h3, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h0, h208, h221, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                    · linarith only [h0, h223, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h207, h223, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h226 | h226
            · linarith only [h2, h208, h226, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
              · linarith only [h207, h208, h228, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h230 | h230
                · linarith only [h0, h228, h230, h3, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
                  · linarith only [h2, h232, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h234, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h2, h207, h208, h234, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h237 | h237
          · rcases m.htr 0 2 5 (by decide) (by decide) with h238 | h238
            · linarith only [h0, h238, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h240 | h240
              · rcases m.htr 0 3 5 (by decide) (by decide) with h241 | h241
                · linarith only [h1, h241, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
                  · linarith only [h0, h207, h237, h241, h243, h3, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                    · linarith only [h0, h245, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                      · linarith only [h0, h247, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h207, h237, h241, h247, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h207, h237, h240, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h251 | h251
            · linarith only [h1, h207, h251, h3, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
              · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
                · linarith only [h1, h254, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h253, h254, h256, h3, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                      · linarith only [h237, h258, h260, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h1, h251, h258, h262, h3, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                          · linarith only [h1, h264, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h253, h258, h264, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h267 | h267
                · linarith only [h0, h253, h267, h3, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                  · linarith only [h2, h269, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                    · linarith only [h0, h207, h271, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                      · linarith only [h0, h237, h273, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                        · linarith only [h1, h271, h275, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                          · linarith only [h1, h253, h277, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                            · linarith only [h2, h267, h277, h279, h3, hlam]
                            · linarith only [h2, h271, h277, h279, h3, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h282 | h282
      · rcases m.htr 0 2 3 (by decide) (by decide) with h283 | h283
        · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
          · linarith only [h0, h2, h284, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
            · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
              · linarith only [h1, h2, h287, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                    · linarith only [h0, h2, h291, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2, h283, h291, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2, h283, h287, h289, h290, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                    · linarith only [h0, h296, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h283, h296, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2, h286, h295, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h300 | h300
              · linarith only [h1, h2, h300, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h302 | h302
                · linarith only [h283, h286, h302, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                    · linarith only [h0, h2, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2, h282, h283, h286, h305, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h2, h282, h304, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
          · linarith only [h0, h2, h309, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h311 | h311
            · rcases m.htr 0 3 4 (by decide) (by decide) with h312 | h312
              · linarith only [h1, h2, h312, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
                · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                    · linarith only [h0, h316, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                      · linarith only [h309, h316, h318, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                        · linarith only [h1, h2, h316, h320, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h311, h320, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h2, h282, h315, hlam]
                · linarith only [h283, h311, h314, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h325 | h325
              · linarith only [h1, h2, h325, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
                · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                    · linarith only [h0, h329, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                      · linarith only [h309, h329, h331, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h333 | h333
                        · linarith only [h0, h311, h333, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                          · linarith only [h1, h2, h325, h335, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1, h2, h335, hc13, hlam, hphi, u3elo3]
                  · linarith only [h1, h2, h327, h328, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                    · linarith only [h0, h283, h340, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h1, h340, h342, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                        · linarith only [h0, h311, h344, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                          · linarith only [h1, h325, h346, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1, h2, h340, h346, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h282, h339, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h350 | h350
        · rcases m.htr 0 2 4 (by decide) (by decide) with h351 | h351
          · linarith only [h0, h2, h351, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h353 | h353
            · linarith only [h0, h282, h353, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
              · linarith only [h1, h2, h355, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h357 | h357
                · linarith only [h0, h282, h350, h357, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                    · linarith only [h0, h360, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h282, h350, h359, h360, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                    · linarith only [h0, h2, h359, h363, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h2, h350, h359, h363, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h366 | h366
          · linarith only [h0, h2, h366, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h368 | h368
            · linarith only [h1, h282, h350, h368, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h370 | h370
              · linarith only [h1, h2, h370, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h372 | h372
                · linarith only [h0, h282, h370, h372, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h374 | h374
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                    · linarith only [h0, h375, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h377 | h377
                      · linarith only [h366, h375, h377, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h379 | h379
                        · linarith only [h0, h1, h282, h368, h379, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h381 | h381
                          · linarith only [h1, h282, h350, h370, h374, h381, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h0, h2, h381, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                    · linarith only [h0, h2, h374, h384, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
                      · linarith only [h1, h2, h374, h384, h386, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
                        · linarith only [h1, h2, h374, h384, h388, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                          · linarith only [h1, h2, h374, h390, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h1, h2, h384, h390, hc12, hlam, hphi, ht23, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
