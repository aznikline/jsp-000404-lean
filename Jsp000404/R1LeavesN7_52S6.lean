import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1029 | h1029
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1030 | h1030
    · linarith only [h1, h1030, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1032 | h1032
      · linarith only [h0, h1, h1032, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1034 | h1034
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1035 | h1035
          · linarith only [h0, h1, h1035, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1037 | h1037
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1038 | h1038
              · linarith only [h0, h1, h1034, h1038, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1040 | h1040
                · linarith only [h1032, h1034, h1040, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1042 | h1042
                  · linarith only [h0, h1, h1042, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · linarith only [h1034, h1035, h1042, hc12, hc25, hlam, hphi]
            · linarith only [h0, h1, h1034, h1037, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1046 | h1046
          · linarith only [h1, h1029, h1034, h1046, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1048 | h1048
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1049 | h1049
              · linarith only [h1, h1029, h1049, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1051 | h1051
                · linarith only [h0, h1, h1032, h1051, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1053 | h1053
                  · linarith only [h0, h1, h1034, h1053, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
                    · linarith only [h1029, h1030, h1046, h1053, h1055, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1057 | h1057
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1058 | h1058
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1059 | h1059
                          · linarith only [h1029, h1030, h1049, h1059, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1062 | h1062
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1063 | h1063
                                · linarith only [h1029, h1030, h1053, h1059, h1063, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1065 | h1065
                                  · linarith only [h1029, h1030, h1057, h1058, h1063, h1065, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · rcases h2bigk with h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1034, hc12, hc24, hlam, hphi, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1032, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1034, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1046, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h0, hlam, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1051, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1053, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1055, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      rcases p1067_3 (m.d 0 2) (by simp) with h1078 | h1078
                                      · linarith only [h1078, hlam, p1067_0]
                                      · rcases p1067_3 (m.d 1 2) (by simp) with h1080 | h1080
                                        · linarith only [h1051, h1080, hlam]
                                        · rcases p1067_3 (m.d 2 3) (by simp) with h1082 | h1082
                                          · rcases p1067_3 (m.d 2 4) (by simp) with h1083 | h1083
                                            · linarith only [h1061, h1083, hlam]
                                            · linarith only [h1034, h1083, hlam]
                                          · linarith only [h1082, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      rcases p1067_3 (m.d 0 2) (by simp) with h1087 | h1087
                                      · linarith only [h1032, h1087, hlam]
                                      · linarith only [h0, h1087, hlam]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1034, hc02, hc23, hlam, hphi, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1030, h1055, hc01, hc23, hlam, hphi, ht12, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h0, h1063, hc12, hc45, hlam, hphi, ht23, ht34, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1063, hc12, hc45, hlam, hphi, ht23, ht34, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1061, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1063, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      rcases p1067_3 (m.d 0 2) (by simp) with h1098 | h1098
                                      · linarith only [h1098, hlam, p1067_0]
                                      · rcases p1067_3 (m.d 1 2) (by simp) with h1100 | h1100
                                        · linarith only [h1055, h1100, hlam]
                                        · rcases p1067_3 (m.d 2 3) (by simp) with h1102 | h1102
                                          · rcases p1067_3 (m.d 2 4) (by simp) with h1103 | h1103
                                            · linarith only [h1063, h1103, hlam]
                                            · linarith only [h1034, h1103, hlam]
                                          · linarith only [h1032, h1102, hlam]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      rcases p1067_3 (m.d 0 2) (by simp) with h1107 | h1107
                                      · linarith only [h1046, h1107, hlam]
                                      · linarith only [h0, h1107, hlam]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h1062, hlam, p1067_0]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [h0, h1034, hc12, hc25, hlam, hphi, p1067_1]
                                    · have p1067_0 := h1067c.1
                                      have p1067_1 := h1067c.2.1
                                      have p1067_2 := h1067c.2.2.1
                                      have p1067_3 := h1067c.2.2.2
                                      linarith only [hlam, p1067_0]
                              · linarith only [h0, h1032, h1058, h1062, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h1029, h1030, h1051, h1057, h1061, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                        · linarith only [h1, h1029, h1053, h1058, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1029, h1053, h1057, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1029, h1048, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1118 | h1118
    · linarith only [h1, h1118, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1120 | h1120
      · linarith only [h0, h1, h1120, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1122 | h1122
        · linarith only [h0, h1029, h1122, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1124 | h1124
          · linarith only [h0, h1, h1124, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1126 | h1126
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1127 | h1127
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1128 | h1128
                · linarith only [h0, h1, h1120, h1128, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1130 | h1130
                  · linarith only [h1122, h1127, h1130, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1132 | h1132
                    · linarith only [h0, h1, h1124, h1132, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1135 | h1135
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1136 | h1136
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1137 | h1137
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1138 | h1138
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1139 | h1139
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1140 | h1140
                                  · linarith only [h1, h1126, h1140, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                  · rcases h2bigk with h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h0, h1118, h1134, h1136, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1142_1, u1elo2]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1120, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1122, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1124, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h0, hlam, p1142_1]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1128, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1130, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1132, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      rcases p1142_3 (m.d 0 2) (by simp) with h1153 | h1153
                                      · linarith only [h1153, hlam, p1142_0]
                                      · rcases p1142_3 (m.d 1 2) (by simp) with h1155 | h1155
                                        · linarith only [h1128, h1155, hlam]
                                        · rcases p1142_3 (m.d 2 3) (by simp) with h1157 | h1157
                                          · rcases p1142_3 (m.d 2 4) (by simp) with h1158 | h1158
                                            · linarith only [h1137, h1158, hlam]
                                            · linarith only [h1122, h1158, hlam]
                                          · linarith only [h1157, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      rcases p1142_3 (m.d 0 2) (by simp) with h1162 | h1162
                                      · linarith only [h1120, h1162, hlam]
                                      · linarith only [h0, h1162, hlam]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1118, h1130, h1136, hc01, hc23, hlam, hphi, ht12, p1142_1]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h0, h1118, h1132, hc12, hc23, hlam, hphi, p1142_1]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      rcases p1142_3 (m.d 0 2) (by simp) with h1168 | h1168
                                      · linarith only [h1168, hlam, p1142_0]
                                      · rcases p1142_3 (m.d 1 2) (by simp) with h1170 | h1170
                                        · linarith only [h1130, h1170, hlam]
                                        · rcases p1142_3 (m.d 2 3) (by simp) with h1172 | h1172
                                          · rcases p1142_3 (m.d 2 4) (by simp) with h1173 | h1173
                                            · rcases p1142_3 (m.d 2 5) (by simp) with h1174 | h1174
                                              · linarith only [h1139, h1174, hlam]
                                              · linarith only [h1124, h1174, hlam]
                                            · linarith only [h1173, hlam, p1142_0]
                                          · linarith only [h1120, h1172, hlam]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      rcases p1142_3 (m.d 0 2) (by simp) with h1179 | h1179
                                      · linarith only [h1122, h1179, hlam]
                                      · linarith only [h0, h1179, hlam]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1137, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h0, h1118, h1132, h1137, hc12, hc23, hlam, hphi, p1142_1]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      rcases p1142_3 (m.d 0 2) (by simp) with h1185 | h1185
                                      · linarith only [h1185, hlam, p1142_0]
                                      · rcases p1142_3 (m.d 1 2) (by simp) with h1187 | h1187
                                        · linarith only [h1132, h1187, hlam]
                                        · rcases p1142_3 (m.d 2 3) (by simp) with h1189 | h1189
                                          · rcases p1142_3 (m.d 2 4) (by simp) with h1190 | h1190
                                            · rcases p1142_3 (m.d 2 5) (by simp) with h1191 | h1191
                                              · rcases h4bigk with h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1029, hlam, p1192_1]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1122, hlam, p1192_1]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  rcases p1192_3 (m.d 0 4) (by simp) with h1196 | h1196
                                                  · rcases p1192_3 (m.d 1 4) (by simp) with h1197 | h1197
                                                    · rcases p1192_3 (m.d 2 4) (by simp) with h1198 | h1198
                                                      · rcases p1192_3 (m.d 3 4) (by simp) with h1199 | h1199
                                                        · linarith only [h1126, h1199, hlam]
                                                        · rcases p1192_3 (m.d 4 5) (by simp) with h1201 | h1201
                                                          · linarith only [h1127, h1201, hlam]
                                                          · linarith only [h1140, h1201, hlam]
                                                      · linarith only [h1137, h1198, hlam]
                                                    · linarith only [h1134, h1197, hlam]
                                                  · linarith only [h1126, h1196, hlam]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1029, h1140, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1192_1, u1elo3]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h0, h1029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1192_1, u1elo3]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1130, hlam, p1192_1]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  rcases p1192_3 (m.d 0 4) (by simp) with h1211 | h1211
                                                  · linarith only [h1029, h1211, hlam]
                                                  · linarith only [h1126, h1211, hlam]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1134, h1140, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1192_1, u1elo2]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1127, h1137, h1140, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1192_1]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h0, h1029, h1137, hc12, hc23, hlam, hphi, p1192_1]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  rcases p1192_3 (m.d 0 4) (by simp) with h1218 | h1218
                                                  · linarith only [h1122, h1218, hlam]
                                                  · linarith only [h1126, h1218, hlam]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  rcases p1192_3 (m.d 0 4) (by simp) with h1221 | h1221
                                                  · linarith only [h1122, h1221, hlam]
                                                  · linarith only [h1127, h1221, hlam]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1126, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1134, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1137, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1140, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1127, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1136, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1139, hlam, p1192_0]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [h1029, h1127, h1134, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1192_1, u1elo2]
                                                · have p1192_0 := h1192c.1
                                                  have p1192_1 := h1192c.2.1
                                                  have p1192_2 := h1192c.2.2.1
                                                  have p1192_3 := h1192c.2.2.2
                                                  linarith only [hlam, p1192_0]
                                              · linarith only [h1191, hlam, p1142_0]
                                            · linarith only [h1122, h1190, hlam]
                                          · linarith only [h1120, h1189, hlam]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      rcases p1142_3 (m.d 0 2) (by simp) with h1237 | h1237
                                      · linarith only [h1124, h1237, hlam]
                                      · linarith only [h0, h1237, hlam]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1138, hlam, p1142_0]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [h1139, hlam, p1142_1]
                                    · have p1142_0 := h1142c.1
                                      have p1142_1 := h1142c.2.1
                                      have p1142_2 := h1142c.2.2.1
                                      have p1142_3 := h1142c.2.2.2
                                      linarith only [hlam, p1142_0]
                                · linarith only [h0, h1029, h1122, h1127, h1134, h1139, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h0, h1118, h1128, h1134, h1136, h1138, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1118, h1128, h1134, h1136, h1137, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1029, h1126, h1127, h1136, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h1, h1135, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1126, h1134, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
                · linarith only [h0, h1, h1249, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1251 | h1251
                  · linarith only [h0, h1, h1251, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1253 | h1253
                    · linarith only [h0, h1, h1253, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1255 | h1255
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1256 | h1256
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1257 | h1257
                          · linarith only [h0, h1029, h1127, h1255, h1257, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1029, h1257, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h1256, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1126, h1255, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1262 | h1262
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1263 | h1263
                · linarith only [h0, h1, h1263, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1265 | h1265
                  · linarith only [h0, h1, h1265, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1267 | h1267
                    · linarith only [h0, h1, h1267, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                      · linarith only [h1, h1126, h1269, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h1, h1269, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
                · linarith only [h0, h1, h1272, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1274 | h1274
                  · linarith only [h0, h1, h1274, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1276 | h1276
                    · linarith only [h0, h1, h1276, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1278 | h1278
                      · linarith only [h1, h1126, h1278, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h1, h1278, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1281 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1282 | h1282
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1283 | h1283
    · linarith only [h0, h1283, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1285 | h1285
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1286 | h1286
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1287 | h1287
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1288 | h1288
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1289 | h1289
              · linarith only [h0, h1281, h1288, h1289, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1292 | h1292
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1293 | h1293
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1294 | h1294
                      · linarith only [h1281, h1283, h1293, h1294, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h1281, h1283, h1288, h1293, h1294, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h1282, h1287, h1292, h1293, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1286, h1292, hlam]
                · linarith only [h0, h1285, h1291, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1300 | h1300
              · linarith only [h0, h1282, h1300, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1302 | h1302
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1303 | h1303
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1304 | h1304
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1305 | h1305
                      · linarith only [h1281, h1283, h1288, h1304, h1305, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1307 | h1307
                        · linarith only [h1281, h1283, h1304, h1307, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1309 | h1309
                          · linarith only [h1282, h1283, h1300, h1304, h1309, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1311 | h1311
                            · linarith only [h0, h1285, h1288, h1311, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1313 | h1313
                              · linarith only [h1283, h1302, h1307, h1313, hc01, hlam, hphi, u1elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1315 | h1315
                                · linarith only [h1282, h1283, h1303, h1309, h1315, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1317 | h1317
                                  · linarith only [h1282, h1283, h1302, h1305, h1309, h1317, hc23, hc34, hlam, hphi]
                                  · rcases h2bigk with h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h0, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      rcases p1319_3 (m.d 0 2) (by simp) with h1322 | h1322
                                      · rcases p1319_3 (m.d 1 2) (by simp) with h1323 | h1323
                                        · rcases p1319_3 (m.d 2 3) (by simp) with h1324 | h1324
                                          · linarith only [h1324, hlam, p1319_0]
                                          · rcases p1319_3 (m.d 2 4) (by simp) with h1326 | h1326
                                            · linarith only [h1286, h1326, hlam]
                                            · linarith only [h1311, h1326, hlam]
                                        · linarith only [h1302, h1323, hlam]
                                      · linarith only [h1322, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      rcases p1319_3 (m.d 0 2) (by simp) with h1331 | h1331
                                      · rcases p1319_3 (m.d 1 2) (by simp) with h1332 | h1332
                                        · rcases p1319_3 (m.d 2 3) (by simp) with h1333 | h1333
                                          · linarith only [h1285, h1333, hlam]
                                          · rcases p1319_3 (m.d 2 4) (by simp) with h1335 | h1335
                                            · linarith only [h1335, hlam, p1319_0]
                                            · rcases p1319_3 (m.d 2 5) (by simp) with h1337 | h1337
                                              · linarith only [h1287, h1337, hlam]
                                              · linarith only [h1315, h1337, hlam]
                                        · linarith only [h1303, h1332, hlam]
                                      · linarith only [h1331, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p1319_1, u1elo1, u5ehi2]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h0, h1282, h1302, h1305, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1319_1, u1elo1]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      rcases p1319_3 (m.d 0 2) (by simp) with h1345 | h1345
                                      · linarith only [h0, h1345, hlam]
                                      · linarith only [h1285, h1345, hlam]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      rcases p1319_3 (m.d 0 2) (by simp) with h1348 | h1348
                                      · linarith only [h0, h1348, hlam]
                                      · linarith only [h1286, h1348, hlam]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p1319_1, u1elo1, u5ehi2]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1285, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1302, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1311, hlam, p1319_1]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1313, hlam, p1319_1]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1286, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1303, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1282, h1283, h1303, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1319_1, u1elo4]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1315, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1287, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h1304, hlam, p1319_0]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h0, h1287, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1319_1, u1elo1]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [h0, h1287, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1319_1, u1elo1]
                                    · have p1319_0 := h1319c.1
                                      have p1319_1 := h1319c.2.1
                                      have p1319_2 := h1319c.2.2.1
                                      have p1319_3 := h1319c.2.2.2
                                      linarith only [hlam, p1319_0]
                    · linarith only [h0, h1287, h1304, hlam]
                  · linarith only [h0, h1286, h1303, hlam]
                · linarith only [h0, h1285, h1302, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1370 | h1370
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1371 | h1371
              · linarith only [h0, h1282, h1371, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1375 | h1375
                    · linarith only [h0, h1287, h1375, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1377 | h1377
                      · linarith only [h0, h1281, h1375, h1377, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1281, h1370, h1375, h1377, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h1281, h1286, h1370, h1374, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1285, h1373, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1382 | h1382
              · linarith only [h0, h1282, h1382, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1384 | h1384
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1385 | h1385
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1386 | h1386
                    · linarith only [h0, h1287, h1386, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1388 | h1388
                      · linarith only [h1281, h1370, h1388, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1390 | h1390
                        · linarith only [h0, h1282, h1388, h1390, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1392 | h1392
                          · linarith only [h0, h1282, h1287, h1382, h1392, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1394 | h1394
                            · linarith only [h1281, h1370, h1384, h1394, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1396 | h1396
                              · linarith only [h0, h1282, h1384, h1386, h1388, h1390, h1396, hlam]
                              · linarith only [h0, h1282, h1386, h1388, h1396, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h1281, h1286, h1384, h1385, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1285, h1384, hlam]
        · linarith only [h0, h1282, h1286, hlam]
      · linarith only [h0, h1281, h1285, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1403 | h1403
    · linarith only [h0, h1403, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1405 | h1405
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1406 | h1406
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1407 | h1407
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1408 | h1408
            · linarith only [h1281, h1282, h1408, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1410 | h1410
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1411 | h1411
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1412 | h1412
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1413 | h1413
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1414 | h1414
                      · linarith only [h1281, h1282, h1408, h1412, h1414, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1416 | h1416
                        · linarith only [h1281, h1282, h1412, h1416, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1418 | h1418
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1419 | h1419
                            · linarith only [h1281, h1403, h1405, h1414, h1418, h1419, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1421 | h1421
                              · linarith only [h1281, h1403, h1411, h1416, h1421, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1423 | h1423
                                · linarith only [h0, h1406, h1423, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1425 | h1425
                                  · rcases h2bigk with h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h0, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      rcases p1426_3 (m.d 0 2) (by simp) with h1429 | h1429
                                      · rcases p1426_3 (m.d 1 2) (by simp) with h1430 | h1430
                                        · rcases p1426_3 (m.d 2 3) (by simp) with h1431 | h1431
                                          · linarith only [h1431, hlam, p1426_0]
                                          · rcases p1426_3 (m.d 2 4) (by simp) with h1433 | h1433
                                            · linarith only [h1406, h1433, hlam]
                                            · linarith only [h1419, h1433, hlam]
                                        · linarith only [h1411, h1430, hlam]
                                      · linarith only [h1429, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      rcases p1426_3 (m.d 0 2) (by simp) with h1438 | h1438
                                      · rcases p1426_3 (m.d 1 2) (by simp) with h1439 | h1439
                                        · rcases p1426_3 (m.d 2 3) (by simp) with h1440 | h1440
                                          · linarith only [h1405, h1440, hlam]
                                          · rcases p1426_3 (m.d 2 4) (by simp) with h1442 | h1442
                                            · linarith only [h1442, hlam, p1426_0]
                                            · rcases p1426_3 (m.d 2 5) (by simp) with h1444 | h1444
                                              · linarith only [h1407, h1444, hlam]
                                              · linarith only [h1423, h1444, hlam]
                                        · linarith only [h1412, h1439, hlam]
                                      · linarith only [h1438, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p1426_1, u1elo1, u5ehi2]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h0, h1281, h1411, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1426_1, u1elo1]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      rcases p1426_3 (m.d 0 2) (by simp) with h1452 | h1452
                                      · linarith only [h0, h1452, hlam]
                                      · linarith only [h1405, h1452, hlam]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      rcases p1426_3 (m.d 0 2) (by simp) with h1455 | h1455
                                      · linarith only [h0, h1455, hlam]
                                      · linarith only [h1406, h1455, hlam]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p1426_1, u1elo1, u5ehi2]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1405, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1411, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1419, hlam, p1426_1]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1421, hlam, p1426_1]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1406, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1412, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1406, h1410, h1423, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1426_1]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1423, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1407, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h1413, hlam, p1426_0]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h0, h1407, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1426_1, u1elo1]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [h0, h1406, h1410, h1423, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1426_1, u1elo1]
                                    · have p1426_0 := h1426c.1
                                      have p1426_1 := h1426c.2.1
                                      have p1426_2 := h1426c.2.2.1
                                      have p1426_3 := h1426c.2.2.2
                                      linarith only [hlam, p1426_0]
                                  · linarith only [h1282, h1410, h1414, h1425, hlam]
                          · linarith only [h1282, h1410, h1418, hlam]
                    · linarith only [h0, h1407, h1413, hlam]
                  · linarith only [h0, h1406, h1412, hlam]
                · linarith only [h0, h1405, h1411, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1479 | h1479
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1480 | h1480
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1481 | h1481
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
                      · linarith only [h1281, h1282, h1482, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1484 | h1484
                        · linarith only [h1281, h1282, h1480, h1484, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1486 | h1486
                          · linarith only [h1281, h1282, h1410, h1479, h1480, h1486, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h1281, h1282, h1479, h1486, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1407, h1481, hlam]
                  · linarith only [h0, h1282, h1406, h1407, h1480, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                · linarith only [h0, h1281, h1405, h1479, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1492 | h1492
            · linarith only [h1281, h1282, h1492, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1494 | h1494
              · linarith only [h1406, h1407, h1494, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1496 | h1496
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1497 | h1497
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1498 | h1498
                    · linarith only [h1406, h1407, h1498, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1500 | h1500
                      · linarith only [h1281, h1492, h1500, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1502 | h1502
                        · linarith only [h1281, h1282, h1497, h1498, h1502, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
                          · linarith only [h1282, h1494, h1497, h1498, h1504, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h1281, h1282, h1496, h1504, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1281, h1406, h1496, h1497, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1405, h1496, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1509 | h1509
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1510 | h1510
            · linarith only [h0, h1281, h1406, h1509, h1510, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1512 | h1512
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1513 | h1513
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1514 | h1514
                  · linarith only [h1406, h1509, h1514, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1516 | h1516
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1517 | h1517
                      · linarith only [h1281, h1403, h1510, h1514, h1516, h1517, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1519 | h1519
                        · linarith only [h1281, h1403, h1514, h1516, h1519, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1521 | h1521
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1522 | h1522
                            · linarith only [h1281, h1403, h1513, h1514, h1516, h1517, h1522, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h1281, h1403, h1514, h1516, h1522, hc13, hc34, hlam, hphi]
                          · linarith only [h1281, h1403, h1512, h1513, h1514, h1516, h1521, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1281, h1509, h1516, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1405, h1513, hlam]
              · linarith only [h1406, h1509, h1512, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1529 | h1529
            · linarith only [h0, h1281, h1406, h1529, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1531 | h1531
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1532 | h1532
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1533 | h1533
                  · linarith only [h0, h1406, h1533, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1535 | h1535
                    · linarith only [h0, h1281, h1509, h1532, h1533, h1535, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1537 | h1537
                      · linarith only [h1281, h1529, h1537, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1539 | h1539
                        · linarith only [h0, h1281, h1533, h1539, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1541 | h1541
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1542 | h1542
                            · linarith only [h0, h1281, h1405, h1509, h1535, h1537, h1541, h1542, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h1281, h1532, h1533, h1542, hc23, hc34, hlam, hphi]
                          · linarith only [h1281, h1282, h1531, h1532, h1541, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1405, h1532, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1547 | h1547
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1548 | h1548
                  · linarith only [h0, h1281, h1406, h1547, h1548, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1550 | h1550
                    · linarith only [h0, h1281, h1509, h1547, h1548, h1550, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1552 | h1552
                      · linarith only [h0, h1281, h1548, h1552, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1554 | h1554
                        · linarith only [h0, h1281, h1548, h1554, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1556 | h1556
                          · linarith only [h1281, h1282, h1531, h1547, h1556, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h1281, h1282, h1547, h1556, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1281, h1405, h1406, h1531, h1547, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h1281, h1405, hlam]

end R2N4
