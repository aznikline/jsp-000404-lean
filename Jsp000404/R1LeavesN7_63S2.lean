import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S0
import Jsp000404.R1LeavesN7_63S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3024000 in
theorem r1l7_10_12_23_L_0_L_I_M_LI_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h508 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h992 | h992
  · rcases m.htr 0 2 4 (by decide) (by decide) with h993 | h993
    · rcases m.htr 0 2 5 (by decide) (by decide) with h994 | h994
      · rcases m.htr 0 3 4 (by decide) (by decide) with h995 | h995
        · rcases m.htr 0 3 5 (by decide) (by decide) with h996 | h996
          · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
            · rcases m.htr 1 2 4 (by decide) (by decide) with h998 | h998
              · rcases m.htr 1 2 5 (by decide) (by decide) with h999 | h999
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1001 | h1001
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1002 | h1002
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1003 | h1003
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1004 | h1004
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1005 | h1005
                            · linarith only [h1002, h1005, h992, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1002, h1004, h1005, h992, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1008 | h1008
                            · linarith only [h1004, h1008, h508, h995, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases h2bigk with h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h0, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1003, hc35, hlam, hphi, ht0b, ht5b, p1010_1, u0elo1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 2) (by simp) with h1014 | h1014
                                · rcases p1010_3 (m.d 1 2) (by simp) with h1015 | h1015
                                  · rcases p1010_3 (m.d 2 3) (by simp) with h1016 | h1016
                                    · linarith only [h1016, h992, hlam]
                                    · linarith only [h1002, h1016, hlam]
                                  · linarith only [h1015, h998, hlam]
                                · linarith only [h1014, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 2) (by simp) with h1021 | h1021
                                · rcases p1010_3 (m.d 1 2) (by simp) with h1022 | h1022
                                  · rcases p1010_3 (m.d 2 3) (by simp) with h1023 | h1023
                                    · linarith only [h1023, h992, hlam]
                                    · linarith only [h1003, h1023, hlam]
                                  · linarith only [h1022, h999, hlam]
                                · linarith only [h1021, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1003, h1008, h992, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 2) (by simp) with h1030 | h1030
                                · linarith only [h0, h1030, hlam]
                                · linarith only [h1030, h992, hlam]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 2) (by simp) with h1033 | h1033
                                · linarith only [h0, h1033, hlam]
                                · linarith only [h1033, h993, hlam]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 2) (by simp) with h1036 | h1036
                                · linarith only [h0, h1036, hlam]
                                · linarith only [h1036, h994, hlam]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h992, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h997, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1002, h992, hc34, hlam, hphi, ht0b, ht45, ht5b, p1010_1, u0elo1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1003, h1008, h992, hc34, hlam, hphi, ht0b, ht45, ht5b, p1010_1, u0elo1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h993, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h998, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1002, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1004, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h994, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h999, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1003, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1002, h994, hc34, hlam, hphi, ht0b, ht45, ht5b, p1010_1, u0elo1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                        · linarith only [h1003, h508, h996, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1002, h508, h995, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1001, h508, h996, hlam]
                  · linarith only [h1000, h508, h995, hlam]
                · linarith only [h0, h994, h999, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h993, h998, hlam]
            · linarith only [h0, h997, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1061 | h1061
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1062 | h1062
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1063 | h1063
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1064 | h1064
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1065 | h1065
                    · linarith only [h1065, h996, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1065, h508, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1064, h508, h995, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1063, h994, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1062, h993, h995, h996, hc02, hlam, hphi, ht23, u3elo4]
            · linarith only [h0, h1061, h992, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1072 | h1072
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1073 | h1073
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1074 | h1074
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1076 | h1076
                  · linarith only [h1076, h995, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1076, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1075, h994, hlam]
              · linarith only [h0, h1074, h993, hlam]
            · linarith only [h0, h1073, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1082 | h1082
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1083 | h1083
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1084 | h1084
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1085 | h1085
                  · linarith only [h1085, h995, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1085, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1084, h994, hlam]
              · linarith only [h0, h1083, h993, hlam]
            · linarith only [h0, h1072, h1082, h992, hc02, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1091 | h1091
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
          · linarith only [h1092, h992, h994, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1094 | h1094
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1095 | h1095
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1097 | h1097
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1098 | h1098
                    · linarith only [h1092, h1098, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1098, h508, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1091, h1097, h508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1102 | h1102
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1103 | h1103
                    · linarith only [h1092, h1103, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1103, h508, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1091, h1102, h508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h1095, h993, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1094, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1109 | h1109
          · linarith only [h1091, h1109, h993, h994, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
                  · linarith only [h1091, h1114, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1114, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1117 | h1117
                  · linarith only [h1091, h1117, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1117, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h1112, h993, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1111, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1122 | h1122
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1123 | h1123
        · linarith only [h1123, h992, h993, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1126 | h1126
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1127 | h1127
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1128 | h1128
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1129 | h1129
                  · linarith only [h1123, h1129, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1129, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1122, h1127, h1128, h993, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                  · linarith only [h1123, h1125, h1126, h1127, h1134, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h1134, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1122, h1125, h1133, hc01, hlam, hphi, ht12, ht23, u3elo0]
            · linarith only [h0, h1126, h992, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1139 | h1139
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1140 | h1140
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1141 | h1141
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1142 | h1142
                  · linarith only [h1123, h1142, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1142, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1122, h1140, h1141, h993, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1147 | h1147
                  · linarith only [h1123, h1147, h992, h993, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1147, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1122, h1139, h1146, h508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1139, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1152 | h1152
        · linarith only [h1152, h992, h993, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1154 | h1154
          · linarith only [h1122, h1152, h1154, h992, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1156 | h1156
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1157 | h1157
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1158 | h1158
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1159 | h1159
                  · linarith only [h1152, h1159, h508, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1159, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1157, h1158, h992, h993, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1163 | h1163
                · linarith only [h1122, h1157, h1163, h992, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h1152, h1165, h508, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1165, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h1156, h992, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1169 | h1169
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1170 | h1170
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1171 | h1171
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1172 | h1172
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1173 | h1173
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1175 | h1175
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1176 | h1176
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1177 | h1177
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1178 | h1178
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1179 | h1179
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1180 | h1180
                          · linarith only [h1169, h1173, h1180, h992, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1182 | h1182
                            · linarith only [h1171, h1180, h1182, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h0, hlam, p1184_1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h992, hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1173, h1178, h992, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1184_1, u3elo1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1173, h992, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1184_1, u3elo1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                rcases p1184_3 (m.d 0 2) (by simp) with h1190 | h1190
                                · linarith only [h0, h1190, hlam]
                                · rcases p1184_3 (m.d 1 2) (by simp) with h1192 | h1192
                                  · rcases p1184_3 (m.d 2 3) (by simp) with h1193 | h1193
                                    · linarith only [h1173, h1193, hlam]
                                    · linarith only [h1193, h992, hlam]
                                  · linarith only [h0, h1192, hlam]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h0, h992, hc01, hc12, hlam, hphi, p1184_1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1170, h1173, h1180, h992, hlam, p1184_2]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1170, h1173, h992, hlam, p1184_2]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1170, h1173, h1178, h1180, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1173, hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                rcases p1184_3 (m.d 0 2) (by simp) with h1204 | h1204
                                · linarith only [h1204, h992, hlam]
                                · linarith only [h1169, h1204, hlam]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                rcases p1184_3 (m.d 0 2) (by simp) with h1207 | h1207
                                · linarith only [h1207, h992, hlam]
                                · linarith only [h1170, h1207, hlam]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1169, hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1174, hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1178, hlam, p1184_1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1180, hlam, p1184_1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1170, hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1175, hlam, p1184_0]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1179, hlam, p1184_1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [h1170, h1178, hc34, hlam, hphi, ht0b, ht45, ht5b, p1184_1, u0elo1]
                              · have p1184_0 := h1184c.1
                                have p1184_1 := h1184c.2.1
                                have p1184_2 := h1184c.2.2.1
                                have p1184_3 := h1184c.2.2.2
                                linarith only [hlam, p1184_0]
                        · linarith only [h1179, h992, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h1169, h1178, h992, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h1170, h1172, h1177, h992, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1169, h1171, h1173, h1176, h992, hlam]
                · linarith only [h1170, h1173, h1175, h992, hc12, hlam, hphi, ht23, u3elo1]
              · linarith only [h1173, h1174, h992, hc02, hc24, hlam, hphi]
            · linarith only [h0, h1173, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h1170, h1172, h992, hlam]
        · linarith only [h1169, h1171, h992, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1229 | h1229
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1230 | h1230
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1231 | h1231
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1232 | h1232
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1233 | h1233
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1234 | h1234
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1237 | h1237
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1238 | h1238
                          · linarith only [h1169, h1231, h1238, h992, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1240 | h1240
                            · linarith only [h1169, h1170, h1236, h1238, h1240, hlam]
                            · rcases h2bigk with h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h992, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1170, h1233, h1235, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1242_1, u3elo1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1170, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                rcases p1242_3 (m.d 0 2) (by simp) with h1248 | h1248
                                · linarith only [h0, h1248, hlam]
                                · rcases p1242_3 (m.d 1 2) (by simp) with h1250 | h1250
                                  · rcases p1242_3 (m.d 2 3) (by simp) with h1251 | h1251
                                    · linarith only [h1231, h1251, hlam]
                                    · linarith only [h1251, h992, hlam]
                                  · linarith only [h0, h1250, hlam]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, h992, hc01, hc12, hlam, hphi, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1169, h1231, h992, hlam, p1242_2]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1169, h1170, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1169, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1242_1, u3elo2]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1231, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                rcases p1242_3 (m.d 0 2) (by simp) with h1262 | h1262
                                · linarith only [h1262, h992, hlam]
                                · linarith only [h1169, h1262, hlam]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1169, h1170, h1231, h1236, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1242_1, u3elo1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1169, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1232, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1236, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1238, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1169, h1236, h1238, hc34, hc45, hlam, hphi, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1233, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1237, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                rcases p1242_3 (m.d 0 2) (by simp) with h1274 | h1274
                                · linarith only [h1170, h1274, hlam]
                                · linarith only [h1169, h1274, hlam]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                        · linarith only [h1230, h1237, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1236, h992, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1230, h1235, hc13, hlam, hphi, u3elo0]
                  · linarith only [h1169, h1229, h1231, h1234, h992, hlam]
                · linarith only [h1169, h1231, h1233, h992, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h1169, h1231, h1232, h992, hlam]
            · linarith only [h0, h1231, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1286 | h1286
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1287 | h1287
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1289 | h1289
                    · linarith only [h1169, h1230, h1289, h992, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h1289, h508, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1169, h1229, h1285, h1288, h992, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1169, h1285, h1287, h992, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h1169, h1285, h1286, h992, hlam]
            · linarith only [h0, h1285, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h1169, h1229, h992, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1297 | h1297
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1298 | h1298
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1299 | h1299
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1300 | h1300
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1301 | h1301
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1302 | h1302
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1303 | h1303
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1304 | h1304
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1305 | h1305
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1306 | h1306
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1307 | h1307
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1308 | h1308
                            · rcases h2bigk with h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h0, hlam, p1309_1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h992, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1169, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1300, h1306, h1308, h992, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1309_1, u3elo1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                rcases p1309_3 (m.d 0 2) (by simp) with h1315 | h1315
                                · linarith only [h0, h1315, hlam]
                                · rcases p1309_3 (m.d 1 2) (by simp) with h1317 | h1317
                                  · rcases p1309_3 (m.d 2 3) (by simp) with h1318 | h1318
                                    · linarith only [h1300, h1318, hlam]
                                    · linarith only [h1318, h992, hlam]
                                  · linarith only [h0, h1317, hlam]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h0, h992, hc01, hc12, hlam, hphi, p1309_1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1169, h1297, h1306, h1308, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1309_1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1297, h1300, h992, hlam, p1309_2]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1297, h1306, h1308, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1309_1, u3elo2]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1300, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1169, h1297, h1300, h1306, h1308, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1309_1, u3elo1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                rcases p1309_3 (m.d 0 2) (by simp) with h1330 | h1330
                                · linarith only [h1330, h992, hlam]
                                · linarith only [h1297, h1330, hlam]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1297, h1301, h1306, h1308, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1309_1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1301, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1305, hlam, p1309_1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                rcases p1309_3 (m.d 0 2) (by simp) with h1337 | h1337
                                · linarith only [h1169, h1337, hlam]
                                · linarith only [h1297, h1337, hlam]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1297, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1302, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1306, hlam, p1309_1]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [h1307, hlam, p1309_0]
                              · have p1309_0 := h1309c.1
                                have p1309_1 := h1309c.2.1
                                have p1309_2 := h1309c.2.2.1
                                have p1309_3 := h1309c.2.2.2
                                linarith only [hlam, p1309_0]
                            · linarith only [h1297, h1300, h1307, h1308, h992, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1169, h1297, h1307, hlam]
                        · linarith only [h1306, h992, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h1297, h1305, h992, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1169, h1297, h1299, h1301, h1303, h1304, hlam]
                  · linarith only [h1298, h1303, hc13, hlam, hphi, u3elo0]
                · linarith only [h1297, h1302, h992, hc12, hc23, hlam, hphi]
              · linarith only [h1300, h1301, h992, hc02, hc24, hlam, hphi]
            · linarith only [h0, h1300, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h1169, h1297, h1298, h1299, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1355 | h1355
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1356 | h1356
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1357 | h1357
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1358 | h1358
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1359 | h1359
                  · linarith only [h1298, h1359, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1359, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1297, h1356, h1358, h992, hlam]
              · linarith only [h1297, h1356, h1357, h992, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h0, h1356, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h1297, h1355, h992, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1366 | h1366
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1367 | h1367
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1368 | h1368
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1369 | h1369
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1370 | h1370
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1371 | h1371
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1372 | h1372
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1373 | h1373
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1374 | h1374
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1375 | h1375
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1376 | h1376
                            · rcases h2bigk with h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, hlam, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h992, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1169, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1297, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                rcases p1377_3 (m.d 0 2) (by simp) with h1383 | h1383
                                · linarith only [h0, h1383, hlam]
                                · rcases p1377_3 (m.d 1 2) (by simp) with h1385 | h1385
                                  · rcases p1377_3 (m.d 2 3) (by simp) with h1386 | h1386
                                    · linarith only [h1368, h1386, hlam]
                                    · linarith only [h1386, h992, hlam]
                                  · linarith only [h0, h1385, hlam]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h992, hc01, hc12, hlam, hphi, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1169, hc01, hc12, hlam, hphi, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1297, hc01, hc12, hlam, hphi, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1377_1, u3elo2]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1368, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1297, h1368, h1375, hc01, hlam, hphi, ht12, ht23, p1377_1, u3elo1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1297, h1368, hc01, hlam, hphi, ht12, ht23, p1377_1, u3elo1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1369, hc01, hc12, hlam, hphi, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1369, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1373, hlam, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1297, h1369, h1371, hc01, hlam, hphi, ht12, ht23, p1377_1, u3elo1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h0, h1370, hc01, hc12, hlam, hphi, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1370, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1374, hlam, p1377_1]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [h1375, hlam, p1377_0]
                              · have p1377_0 := h1377c.1
                                have p1377_1 := h1377c.2.1
                                have p1377_2 := h1377c.2.2.1
                                have p1377_3 := h1377c.2.2.2
                                linarith only [hlam, p1377_0]
                            · rcases h2bigk with h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, hlam, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h992, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1169, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1297, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                rcases p1409_3 (m.d 0 2) (by simp) with h1415 | h1415
                                · linarith only [h0, h1415, hlam]
                                · rcases p1409_3 (m.d 1 2) (by simp) with h1417 | h1417
                                  · rcases p1409_3 (m.d 2 3) (by simp) with h1418 | h1418
                                    · linarith only [h1368, h1418, hlam]
                                    · linarith only [h1418, h992, hlam]
                                  · linarith only [h0, h1417, hlam]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, h992, hc01, hc12, hlam, hphi, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1375, h1376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, h1297, hc01, hc12, hlam, hphi, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1409_1, u3elo2]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1368, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1368, h1375, h1376, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1409_1, u3elo1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, h1297, h1368, hc01, hlam, hphi, ht12, ht23, p1409_1, u3elo1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, h1369, hc01, hc12, hlam, hphi, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1369, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1373, hlam, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, h1297, h1369, h1371, hc01, hlam, hphi, ht12, ht23, p1409_1, u3elo1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h0, h1370, hc01, hc12, hlam, hphi, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1370, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1374, hlam, p1409_1]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [h1375, hlam, p1409_0]
                              · have p1409_0 := h1409c.1
                                have p1409_1 := h1409c.2.1
                                have p1409_2 := h1409c.2.2.1
                                have p1409_3 := h1409c.2.2.2
                                linarith only [hlam, p1409_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1441 | h1441
                            · linarith only [h0, h1169, h1375, h1441, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · rcases h2bigk with h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, hlam, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h992, hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1169, hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1297, hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                rcases p1443_3 (m.d 0 2) (by simp) with h1449 | h1449
                                · linarith only [h0, h1449, hlam]
                                · rcases p1443_3 (m.d 1 2) (by simp) with h1451 | h1451
                                  · rcases p1443_3 (m.d 2 3) (by simp) with h1452 | h1452
                                    · linarith only [h1368, h1452, hlam]
                                    · linarith only [h1452, h992, hlam]
                                  · linarith only [h0, h1451, hlam]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h992, hc01, hc12, hlam, hphi, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1169, hc01, hc12, hlam, hphi, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1297, hc01, hc12, hlam, hphi, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1443_1, u3elo2]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1368, hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1169, h1368, hc01, hlam, hphi, ht12, ht23, p1443_1, u3elo1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1297, h1368, hc01, hlam, hphi, ht12, ht23, p1443_1, u3elo1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1375, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1369, hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1373, hlam, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1375, hlam, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1370, hc01, hc12, hlam, hphi, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1370, hlam, p1443_0]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h1374, hlam, p1443_1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [h0, h1169, h1370, h1372, hc01, hlam, hphi, ht12, ht23, p1443_1, u3elo1]
                              · have p1443_0 := h1443c.1
                                have p1443_1 := h1443c.2.1
                                have p1443_2 := h1443c.2.2.1
                                have p1443_3 := h1443c.2.2.2
                                linarith only [hlam, p1443_0]
                        · linarith only [h0, h1374, h992, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1373, h992, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1372, h508, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1371, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1368, h1370, h992, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1368, h1369, h992, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h1368, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1482 | h1482
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1483 | h1483
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1484 | h1484
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1485 | h1485
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1486 | h1486
                    · linarith only [h1367, h1486, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1486, h508, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1366, h1482, h1485, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h1482, h1484, h992, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1482, h1483, h992, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h1482, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1494 | h1494
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1495 | h1495
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1496 | h1496
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1497 | h1497
                  · linarith only [h1366, h1497, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1497, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1169, h1495, h1496, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1494, h1495, h992, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h1494, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1503 | h1503
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1504 | h1504
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1505 | h1505
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1506 | h1506
                  · linarith only [h1366, h1506, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1506, h508, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1503, h1505, h992, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1503, h1504, h992, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h1503, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3024000 in
theorem r1l7_10_12_23_L_0_L_I_M_LI_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h508 | h508
  · exact r1l7_10_12_23_L_0_L_I_M_LI_x1_x0 m hb0 hb2 hb3 h0 h508
  · exact r1l7_10_12_23_L_0_L_I_M_LI_x1_x1 m hb0 hb2 hb3 h0 h508

set_option maxHeartbeats 3024000 in
theorem r1l7_10_12_23_L_0_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_0_L_I_M_LI_x0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_0_L_I_M_LI_x1 m hb0 hb2 hb3 h0

end R2N4
