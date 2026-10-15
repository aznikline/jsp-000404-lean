import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S0
import Jsp000404.R1LeavesN7_33S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h822 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1034 | h1034
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1035 | h1035
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1036 | h1036
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1037 | h1037
        · linarith only [h0, h1037, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1039 | h1039
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1040 | h1040
            · linarith only [h0, h1040, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1042 | h1042
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1044 | h1044
                  · linarith only [h1039, h1040, h1044, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1046 | h1046
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1047 | h1047
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1048 | h1048
                        · linarith only [h0, h1039, h1044, h1048, h822, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1039, h1046, h1048, h822, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h1, h1039, h1040, h1043, h1046, h1047, h4, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h1043, h1046, h4, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1042, h1043, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1037, h1039, h1042, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
            · linarith only [h1039, h1055, h822, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1057 | h1057
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1058 | h1058
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1059 | h1059
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1060 | h1060
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1061 | h1061
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1062 | h1062
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
                          · rcases h1bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1066 | h1066
                              · rcases p1064_3 (m.d 1 2) (by simp) with h1067 | h1067
                                · linarith only [h1067, hlam, p1064_0]
                                · rcases p1064_3 (m.d 1 3) (by simp) with h1069 | h1069
                                  · linarith only [h1, h1069, hlam]
                                  · linarith only [h1037, h1069, hlam]
                              · linarith only [h1066, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1057, h1063, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1074 | h1074
                              · rcases p1064_3 (m.d 1 2) (by simp) with h1075 | h1075
                                · linarith only [h0, h1075, hlam]
                                · rcases p1064_3 (m.d 1 3) (by simp) with h1077 | h1077
                                  · linarith only [h1, h1077, hlam]
                                  · linarith only [h1057, h1077, hlam]
                              · linarith only [h1074, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1081 | h1081
                              · rcases p1064_3 (m.d 1 2) (by simp) with h1082 | h1082
                                · linarith only [h0, h1082, hlam]
                                · rcases p1064_3 (m.d 1 3) (by simp) with h1084 | h1084
                                  · linarith only [h1, h1084, hlam]
                                  · linarith only [h1058, h1084, hlam]
                              · linarith only [h1081, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1037, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1039, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1055, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1094 | h1094
                              · rcases p1064_3 (m.d 1 2) (by simp) with h1095 | h1095
                                · linarith only [h1037, h1095, hlam]
                                · rcases p1064_3 (m.d 1 3) (by simp) with h1097 | h1097
                                  · rcases p1064_3 (m.d 1 4) (by simp) with h1098 | h1098
                                    · linarith only [h1057, h1098, hlam]
                                    · linarith only [h1039, h1098, hlam]
                                  · linarith only [h1037, h1097, hlam]
                              · linarith only [h0, h1094, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1, h1058, h1059, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1, h1058, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h2, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1107 | h1107
                              · rcases p1064_3 (m.d 1 2) (by simp) with h1108 | h1108
                                · linarith only [h1039, h1108, hlam]
                                · rcases p1064_3 (m.d 1 3) (by simp) with h1110 | h1110
                                  · rcases p1064_3 (m.d 1 4) (by simp) with h1111 | h1111
                                    · rcases p1064_3 (m.d 1 5) (by simp) with h1112 | h1112
                                      · linarith only [h1059, h1112, hlam]
                                      · linarith only [h1055, h1112, hlam]
                                    · linarith only [h1039, h1111, hlam]
                                  · linarith only [h1037, h1110, hlam]
                              · linarith only [h0, h1107, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1057, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1, h1057, h1058, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h3, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1122 | h1122
                              · rcases p1064_3 (m.d 1 2) (by simp) with h1123 | h1123
                                · linarith only [h1055, h1123, hlam]
                                · rcases p1064_3 (m.d 1 3) (by simp) with h1125 | h1125
                                  · rcases p1064_3 (m.d 1 4) (by simp) with h1126 | h1126
                                    · rcases p1064_3 (m.d 1 5) (by simp) with h1127 | h1127
                                      · rcases h5bigk with h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, p1128_1]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h822, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1035, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1128_1, u3ehi4]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          rcases p1128_3 (m.d 0 5) (by simp) with h1133 | h1133
                                          · rcases p1128_3 (m.d 1 5) (by simp) with h1134 | h1134
                                            · linarith only [h1134, h3, hlam]
                                            · linarith only [h1059, h1134, hlam]
                                          · linarith only [h1036, h1133, hlam]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h3, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1055, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1, h1057, h1059, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1128_1, u3ehi4]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1, h1057, h1059, hc01, hc45, hlam, hphi, ht0b, ht5b, p1128_1]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1060, h1062, h3, hc12, hc23, hlam, hphi, p1064_1, p1128_1]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1060, h1062, hc12, hc23, hlam, hphi, p1064_1, p1128_1]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1, h1057, h1059, h1060, h1062, hc01, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, p1128_1, u3ehi4]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          rcases p1128_3 (m.d 0 5) (by simp) with h1147 | h1147
                                          · linarith only [h1147, h822, hlam]
                                          · linarith only [h1036, h1147, hlam]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1035, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1058, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1061, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1, h1034, h1057, h1059, h1063, h4, hc01, hc12, hc23, hc45, hlam, hphi, ht0b, ht5b, p1064_1, p1128_1]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1036, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1059, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1062, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [h1063, hlam, p1128_0]
                                        · have p1128_0 := h1128c.1
                                          have p1128_1 := h1128c.2.1
                                          have p1128_2 := h1128c.2.2.1
                                          have p1128_3 := h1128c.2.2.2
                                          linarith only [hlam, p1128_0]
                                      · linarith only [h1055, h1127, hlam]
                                    · linarith only [h1039, h1126, hlam]
                                  · linarith only [h1037, h1125, hlam]
                              · linarith only [h0, h1122, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1058, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1059, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                          · linarith only [h1, h1057, h1059, h1063, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h1039, h1057, h1059, h1062, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1034, h1058, h1059, h1061, h2, h4, hlam]
                    · linarith only [h1, h1058, h1060, h4, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1171 | h1171
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1172 | h1172
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1173 | h1173
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1174 | h1174
                          · linarith only [h1, h1057, h1059, h1174, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 1) (by simp) with h1178 | h1178
                              · rcases p1176_3 (m.d 1 2) (by simp) with h1179 | h1179
                                · linarith only [h1179, hlam, p1176_0]
                                · rcases p1176_3 (m.d 1 3) (by simp) with h1181 | h1181
                                  · linarith only [h1, h1181, hlam]
                                  · linarith only [h1037, h1181, hlam]
                              · linarith only [h1178, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1057, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi3]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 1) (by simp) with h1186 | h1186
                              · rcases p1176_3 (m.d 1 2) (by simp) with h1187 | h1187
                                · linarith only [h0, h1187, hlam]
                                · rcases p1176_3 (m.d 1 3) (by simp) with h1189 | h1189
                                  · linarith only [h1, h1189, hlam]
                                  · linarith only [h1057, h1189, hlam]
                              · linarith only [h1186, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 1) (by simp) with h1193 | h1193
                              · rcases p1176_3 (m.d 1 2) (by simp) with h1194 | h1194
                                · linarith only [h0, h1194, hlam]
                                · rcases p1176_3 (m.d 1 3) (by simp) with h1196 | h1196
                                  · linarith only [h1, h1196, hlam]
                                  · linarith only [h1058, h1196, hlam]
                              · linarith only [h1193, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h0, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1037, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1039, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1055, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 1) (by simp) with h1206 | h1206
                              · rcases p1176_3 (m.d 1 2) (by simp) with h1207 | h1207
                                · linarith only [h1037, h1207, hlam]
                                · rcases p1176_3 (m.d 1 3) (by simp) with h1209 | h1209
                                  · rcases p1176_3 (m.d 1 4) (by simp) with h1210 | h1210
                                    · linarith only [h1057, h1210, hlam]
                                    · linarith only [h1039, h1210, hlam]
                                  · linarith only [h1037, h1209, hlam]
                              · linarith only [h0, h1206, hlam]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1, h1057, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi3]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1, h1058, h1174, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi3]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h2, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1034, h1036, h1059, h4, hc12, hc23, hlam, hphi, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1057, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1059, hlam, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h3, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1034, h1036, h1059, h4, hc12, hc23, hlam, hphi, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1058, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1034, h1036, h1057, h1059, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1176_1, u3ehi3]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                        · linarith only [h1034, h1036, h1039, h1173, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h1034, h1172, h4, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1034, h1036, h1057, h1059, h1171, h4, hlam]
                · linarith only [h1057, h1058, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1232 | h1232
                · linarith only [h1034, h1057, h1232, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1234 | h1234
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1237 | h1237
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                          · rcases h1bigk with h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              rcases p1239_3 (m.d 0 1) (by simp) with h1241 | h1241
                              · rcases p1239_3 (m.d 1 2) (by simp) with h1242 | h1242
                                · linarith only [h1242, hlam, p1239_0]
                                · rcases p1239_3 (m.d 1 3) (by simp) with h1244 | h1244
                                  · linarith only [h1, h1244, hlam]
                                  · linarith only [h1037, h1244, hlam]
                              · linarith only [h1241, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              rcases p1239_3 (m.d 0 1) (by simp) with h1248 | h1248
                              · rcases p1239_3 (m.d 1 2) (by simp) with h1249 | h1249
                                · linarith only [h0, h1249, hlam]
                                · rcases p1239_3 (m.d 1 3) (by simp) with h1251 | h1251
                                  · linarith only [h1251, hlam, p1239_0]
                                  · rcases p1239_3 (m.d 1 4) (by simp) with h1253 | h1253
                                    · linarith only [h1253, h2, hlam]
                                    · linarith only [h1057, h1253, hlam]
                              · linarith only [h1248, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              rcases p1239_3 (m.d 0 1) (by simp) with h1257 | h1257
                              · rcases p1239_3 (m.d 1 2) (by simp) with h1258 | h1258
                                · linarith only [h0, h1258, hlam]
                                · rcases p1239_3 (m.d 1 3) (by simp) with h1260 | h1260
                                  · linarith only [h1, h1260, hlam]
                                  · rcases p1239_3 (m.d 1 4) (by simp) with h1262 | h1262
                                    · linarith only [h1262, hlam, p1239_0]
                                    · rcases p1239_3 (m.d 1 5) (by simp) with h1264 | h1264
                                      · linarith only [h1264, h3, hlam]
                                      · rcases h5bigk with h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1232, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1266_1, u3ehi1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h822, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1232, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1266_1, u3ehi1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          rcases p1266_3 (m.d 0 5) (by simp) with h1271 | h1271
                                          · rcases p1266_3 (m.d 1 5) (by simp) with h1272 | h1272
                                            · linarith only [h1272, h3, hlam]
                                            · linarith only [h1234, h1272, hlam]
                                          · linarith only [h1036, h1271, hlam]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h3, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1055, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1232, hlam, p1266_1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1266_1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h0, h1235, h1237, h822, hc12, hc23, hlam, hphi, p1266_1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1055, h1235, h1237, hc12, hc23, hlam, hphi, p1266_1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1232, h1235, h1237, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1266_1, u3ehi1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          rcases p1266_3 (m.d 0 5) (by simp) with h1285 | h1285
                                          · linarith only [h1285, h822, hlam]
                                          · linarith only [h1036, h1285, hlam]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1035, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1034, h1232, h1238, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1266_1, u3ehi1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1236, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1034, h1238, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1266_1]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1036, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1234, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1237, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [h1238, hlam, p1266_0]
                                        · have p1266_0 := h1266c.1
                                          have p1266_1 := h1266c.2.1
                                          have p1266_2 := h1266c.2.2.1
                                          have p1266_3 := h1266c.2.2.2
                                          linarith only [hlam, p1266_0]
                              · linarith only [h1257, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              rcases p1239_3 (m.d 0 1) (by simp) with h1299 | h1299
                              · rcases p1239_3 (m.d 1 2) (by simp) with h1300 | h1300
                                · linarith only [h0, h1300, hlam]
                                · rcases p1239_3 (m.d 1 3) (by simp) with h1302 | h1302
                                  · linarith only [h1, h1302, hlam]
                                  · rcases p1239_3 (m.d 1 4) (by simp) with h1304 | h1304
                                    · linarith only [h1304, h2, hlam]
                                    · linarith only [h1234, h1304, hlam]
                              · linarith only [h1299, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1037, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1039, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1055, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1034, h1057, h4, hc12, hc23, hlam, hphi, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1057, hlam, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1232, hlam, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h2, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1034, h1057, h4, hc12, hc23, hlam, hphi, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1034, h1057, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1239_1, u3ehi1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1034, h1057, h1232, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1239_1, u3ehi1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h3, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1034, h1232, h1238, h4, hc12, hc23, hlam, hphi, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1034, h1232, h1238, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1239_1, u3ehi1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1234, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                          · linarith only [h1034, h1036, h1057, h1238, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h1039, h1057, h1234, h1237, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1034, h1236, h4, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1035, h1232, h1235, h4, hc34, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1332 | h1332
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1333 | h1333
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1334 | h1334
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1335 | h1335
                          · linarith only [h1034, h1057, h1234, h1335, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h1057, h1334, h1335, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h1034, h1036, h1039, h1334, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h1035, h1333, h4, hlam]
                    · linarith only [h1035, h1332, h4, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1341 | h1341
        · linarith only [h0, h1035, h1341, h4, h822, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1343 | h1343
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1344 | h1344
            · linarith only [h0, h1344, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1346 | h1346
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1347 | h1347
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1348 | h1348
                  · linarith only [h1036, h1348, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1350 | h1350
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1351 | h1351
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1352 | h1352
                        · linarith only [h0, h1036, h1343, h1351, h1352, h822, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1343, h1350, h1352, h822, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h0, h1343, h1350, h1351, h4, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h1347, h1350, h4, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1035, h1346, h1347, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1034, h1036, h1346, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1359 | h1359
            · linarith only [h0, h1359, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1361 | h1361
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1362 | h1362
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1363 | h1363
                  · linarith only [h1036, h1363, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1365 | h1365
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1366 | h1366
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1367 | h1367
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1368 | h1368
                          · linarith only [h1, h1036, h1361, h1368, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              rcases p1370_3 (m.d 0 1) (by simp) with h1372 | h1372
                              · rcases p1370_3 (m.d 1 2) (by simp) with h1373 | h1373
                                · linarith only [h1373, hlam, p1370_0]
                                · rcases p1370_3 (m.d 1 3) (by simp) with h1375 | h1375
                                  · linarith only [h1, h1375, hlam]
                                  · linarith only [h1341, h1375, hlam]
                              · linarith only [h1372, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1362, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi4]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              rcases p1370_3 (m.d 0 1) (by simp) with h1380 | h1380
                              · rcases p1370_3 (m.d 1 2) (by simp) with h1381 | h1381
                                · linarith only [h0, h1381, hlam]
                                · rcases p1370_3 (m.d 1 3) (by simp) with h1383 | h1383
                                  · linarith only [h1, h1383, hlam]
                                  · linarith only [h1361, h1383, hlam]
                              · linarith only [h1380, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              rcases p1370_3 (m.d 0 1) (by simp) with h1387 | h1387
                              · rcases p1370_3 (m.d 1 2) (by simp) with h1388 | h1388
                                · linarith only [h0, h1388, hlam]
                                · rcases p1370_3 (m.d 1 3) (by simp) with h1390 | h1390
                                  · linarith only [h1, h1390, hlam]
                                  · linarith only [h1362, h1390, hlam]
                              · linarith only [h1387, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h0, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1341, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1343, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1359, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              rcases p1370_3 (m.d 0 1) (by simp) with h1400 | h1400
                              · rcases p1370_3 (m.d 1 2) (by simp) with h1401 | h1401
                                · linarith only [h1341, h1401, hlam]
                                · rcases p1370_3 (m.d 1 3) (by simp) with h1403 | h1403
                                  · rcases p1370_3 (m.d 1 4) (by simp) with h1404 | h1404
                                    · linarith only [h1361, h1404, hlam]
                                    · linarith only [h1343, h1404, hlam]
                                  · linarith only [h1341, h1403, hlam]
                              · linarith only [h0, h1400, hlam]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1, h1361, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi3]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1, h1361, h1363, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi3]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h2, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1036, h1365, h1367, h2, hc12, hc23, hlam, hphi, p1370_1]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1361, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1363, hlam, p1370_1]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h3, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1036, h1365, h1367, h3, hc12, hc23, hlam, hphi, p1370_1]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1362, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1036, h1361, h1365, h1367, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1370_1, u3ehi3]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1422 | h1422
                          · linarith only [h0, h1034, h1367, h1422, h4, h822, hc12, hc23, hlam, hphi]
                          · rcases h1bigk with h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              rcases p1424_3 (m.d 0 1) (by simp) with h1426 | h1426
                              · rcases p1424_3 (m.d 1 2) (by simp) with h1427 | h1427
                                · linarith only [h1427, hlam, p1424_0]
                                · rcases p1424_3 (m.d 1 3) (by simp) with h1429 | h1429
                                  · linarith only [h1, h1429, hlam]
                                  · linarith only [h1341, h1429, hlam]
                              · linarith only [h1426, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1361, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1424_1, u3ehi3]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              rcases p1424_3 (m.d 0 1) (by simp) with h1434 | h1434
                              · rcases p1424_3 (m.d 1 2) (by simp) with h1435 | h1435
                                · linarith only [h0, h1435, hlam]
                                · rcases p1424_3 (m.d 1 3) (by simp) with h1437 | h1437
                                  · linarith only [h1, h1437, hlam]
                                  · linarith only [h1361, h1437, hlam]
                              · linarith only [h1434, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              rcases p1424_3 (m.d 0 1) (by simp) with h1441 | h1441
                              · rcases p1424_3 (m.d 1 2) (by simp) with h1442 | h1442
                                · linarith only [h0, h1442, hlam]
                                · rcases p1424_3 (m.d 1 3) (by simp) with h1444 | h1444
                                  · linarith only [h1, h1444, hlam]
                                  · linarith only [h1362, h1444, hlam]
                              · linarith only [h1441, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h0, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1341, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1343, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1359, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              rcases p1424_3 (m.d 0 1) (by simp) with h1454 | h1454
                              · rcases p1424_3 (m.d 1 2) (by simp) with h1455 | h1455
                                · linarith only [h1341, h1455, hlam]
                                · rcases p1424_3 (m.d 1 3) (by simp) with h1457 | h1457
                                  · rcases p1424_3 (m.d 1 4) (by simp) with h1458 | h1458
                                    · linarith only [h1361, h1458, hlam]
                                    · linarith only [h1343, h1458, hlam]
                                  · linarith only [h1341, h1457, hlam]
                              · linarith only [h0, h1454, hlam]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1, h1361, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1424_1, u3ehi3]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1, h1362, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1424_1, u3ehi4]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h2, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1036, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1424_1]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1361, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1363, hlam, p1424_1]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h3, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              rcases p1424_3 (m.d 0 1) (by simp) with h1472 | h1472
                              · rcases p1424_3 (m.d 1 2) (by simp) with h1473 | h1473
                                · linarith only [h1359, h1473, hlam]
                                · rcases p1424_3 (m.d 1 3) (by simp) with h1475 | h1475
                                  · rcases p1424_3 (m.d 1 4) (by simp) with h1476 | h1476
                                    · linarith only [h1363, h1476, hlam]
                                    · linarith only [h1343, h1476, hlam]
                                  · linarith only [h1341, h1475, hlam]
                              · linarith only [h0, h1472, hlam]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1362, hlam, p1424_0]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [h1361, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1424_1, u3ehi3]
                            · have p1424_0 := h1424c.1
                              have p1424_1 := h1424c.2.1
                              have p1424_2 := h1424c.2.2.1
                              have p1424_3 := h1424c.2.2.2
                              linarith only [hlam, p1424_0]
                      · linarith only [h1034, h1366, h4, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h1361, h1365, h4, hlam]
                · linarith only [h1361, h1362, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1034, h1036, h1361, hc45, hlam, hphi, ht34, u3ehi1]
    · linarith only [h1034, h1035, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1489 | h1489
    · linarith only [h1034, h1489, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1491 | h1491
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1492 | h1492
        · linarith only [h0, h1492, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1494 | h1494
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1495 | h1495
            · linarith only [h0, h1495, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1497 | h1497
              · linarith only [h1, h1489, h1497, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1492, h1494, h1497, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1500 | h1500
            · linarith only [h0, h1500, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1502 | h1502
              · linarith only [h1, h1034, h1502, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1504 | h1504
                · linarith only [h1, h1489, h1504, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1506 | h1506
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1507 | h1507
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1508 | h1508
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1509 | h1509
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1510 | h1510
                          · rcases h1bigk with h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              rcases p1511_3 (m.d 0 1) (by simp) with h1513 | h1513
                              · rcases p1511_3 (m.d 1 2) (by simp) with h1514 | h1514
                                · linarith only [h1514, hlam, p1511_0]
                                · rcases p1511_3 (m.d 1 3) (by simp) with h1516 | h1516
                                  · linarith only [h1, h1516, hlam]
                                  · linarith only [h1492, h1516, hlam]
                              · linarith only [h1513, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              rcases p1511_3 (m.d 0 1) (by simp) with h1520 | h1520
                              · rcases p1511_3 (m.d 1 2) (by simp) with h1521 | h1521
                                · linarith only [h0, h1521, hlam]
                                · rcases p1511_3 (m.d 1 3) (by simp) with h1523 | h1523
                                  · linarith only [h1523, hlam, p1511_0]
                                  · rcases p1511_3 (m.d 1 4) (by simp) with h1525 | h1525
                                    · linarith only [h1525, h2, hlam]
                                    · linarith only [h1502, h1525, hlam]
                              · linarith only [h1520, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              rcases p1511_3 (m.d 0 1) (by simp) with h1529 | h1529
                              · rcases p1511_3 (m.d 1 2) (by simp) with h1530 | h1530
                                · linarith only [h0, h1530, hlam]
                                · rcases p1511_3 (m.d 1 3) (by simp) with h1532 | h1532
                                  · linarith only [h1, h1532, hlam]
                                  · rcases p1511_3 (m.d 1 4) (by simp) with h1534 | h1534
                                    · linarith only [h1534, hlam, p1511_0]
                                    · rcases p1511_3 (m.d 1 5) (by simp) with h1536 | h1536
                                      · linarith only [h1536, h3, hlam]
                                      · rcases h5bigk with h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1491, h1504, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1538_1, u3ehi1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h822, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1489, hlam, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1489, h1507, h1510, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h3, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1500, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1504, hlam, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1506, hc01, hc45, hlam, hphi, ht0b, ht5b, p1511_1, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h0, h1509, h822, hc12, hc24, hlam, hphi, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1500, h1509, hc12, hc24, hlam, hphi, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1, h1489, h1507, h1509, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1538_1, u3ehi1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          rcases p1538_3 (m.d 0 5) (by simp) with h1553 | h1553
                                          · linarith only [h1553, h822, hlam]
                                          · linarith only [h1491, h1553, hlam]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1, h1489, h1510, hc34, hlam, hphi, p1538_1, u3ehi1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1504, h1510, hc34, hlam, hphi, p1538_1, u3ehi1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1508, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1507, h1510, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1538_1]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1491, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1506, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1509, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [h1510, hlam, p1538_0]
                                        · have p1538_0 := h1538c.1
                                          have p1538_1 := h1538c.2.1
                                          have p1538_2 := h1538c.2.2.1
                                          have p1538_3 := h1538c.2.2.2
                                          linarith only [hlam, p1538_0]
                              · linarith only [h1529, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              rcases p1511_3 (m.d 0 1) (by simp) with h1567 | h1567
                              · rcases p1511_3 (m.d 1 2) (by simp) with h1568 | h1568
                                · linarith only [h0, h1568, hlam]
                                · rcases p1511_3 (m.d 1 3) (by simp) with h1570 | h1570
                                  · linarith only [h1, h1570, hlam]
                                  · rcases p1511_3 (m.d 1 4) (by simp) with h1572 | h1572
                                    · linarith only [h1572, h2, hlam]
                                    · linarith only [h1506, h1572, hlam]
                              · linarith only [h1567, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h0, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1492, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1494, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1500, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1, h1034, h1507, hc12, hc23, hlam, hphi, p1511_1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1502, hlam, p1511_1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1504, hlam, p1511_1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h2, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1034, h1507, h2, hc12, hc23, hlam, hphi, p1511_1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1034, h1507, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1511_1, u3ehi1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1034, h1504, h1507, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1511_1, u3ehi1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h3, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1489, h1507, h1510, h3, hc12, hc23, hlam, hphi, p1511_1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1489, h1507, h1510, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1511_1, u3ehi1]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [h1506, hlam, p1511_0]
                            · have p1511_0 := h1511c.1
                              have p1511_1 := h1511c.2.1
                              have p1511_2 := h1511c.2.2.1
                              have p1511_3 := h1511c.2.2.2
                              linarith only [hlam, p1511_0]
                          · linarith only [h1, h1034, h1510, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h1, h1034, h1494, h1506, h1507, h1509, h2, hc01, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h1034, h1507, h1508, hc35, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1599 | h1599
                      · linarith only [h1507, h1599, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1601 | h1601
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1602 | h1602
                          · rcases h1bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              rcases p1603_3 (m.d 0 1) (by simp) with h1605 | h1605
                              · rcases p1603_3 (m.d 1 2) (by simp) with h1606 | h1606
                                · linarith only [h1606, hlam, p1603_0]
                                · rcases p1603_3 (m.d 1 3) (by simp) with h1608 | h1608
                                  · linarith only [h1, h1608, hlam]
                                  · linarith only [h1492, h1608, hlam]
                              · linarith only [h1605, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              rcases p1603_3 (m.d 0 1) (by simp) with h1612 | h1612
                              · rcases p1603_3 (m.d 1 2) (by simp) with h1613 | h1613
                                · linarith only [h0, h1613, hlam]
                                · rcases p1603_3 (m.d 1 3) (by simp) with h1615 | h1615
                                  · linarith only [h1615, hlam, p1603_0]
                                  · rcases p1603_3 (m.d 1 4) (by simp) with h1617 | h1617
                                    · linarith only [h1617, h2, hlam]
                                    · linarith only [h1502, h1617, hlam]
                              · linarith only [h1612, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              rcases p1603_3 (m.d 0 1) (by simp) with h1621 | h1621
                              · rcases p1603_3 (m.d 1 2) (by simp) with h1622 | h1622
                                · linarith only [h0, h1622, hlam]
                                · rcases p1603_3 (m.d 1 3) (by simp) with h1624 | h1624
                                  · linarith only [h1, h1624, hlam]
                                  · rcases p1603_3 (m.d 1 4) (by simp) with h1626 | h1626
                                    · linarith only [h1626, hlam, p1603_0]
                                    · rcases p1603_3 (m.d 1 5) (by simp) with h1628 | h1628
                                      · linarith only [h1628, h3, hlam]
                                      · rcases h5bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1500, h1601, h822, hc12, hc24, hlam, hphi, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h822, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1489, hlam, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          rcases p1630_3 (m.d 0 5) (by simp) with h1635 | h1635
                                          · rcases p1630_3 (m.d 1 5) (by simp) with h1636 | h1636
                                            · linarith only [h1636, h3, hlam]
                                            · linarith only [h1506, h1636, hlam]
                                          · linarith only [h1491, h1635, hlam]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h3, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1500, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1504, hlam, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1507, h1601, h822, hc02, hc34, hlam, hphi, ht23, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1500, h1507, h1601, hc12, hc34, hlam, hphi, ht23, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1599, hlam, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          rcases p1630_3 (m.d 0 5) (by simp) with h1649 | h1649
                                          · linarith only [h1649, h822, hlam]
                                          · linarith only [h1491, h1649, hlam]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1, h1489, hc35, hlam, hphi, p1630_1, u3ehi1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1504, hc35, hlam, hphi, p1630_1, u3ehi1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h0, h822, hc12, hc35, hlam, hphi, ht23, p1630_1]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          rcases p1630_3 (m.d 0 5) (by simp) with h1656 | h1656
                                          · linarith only [h1489, h1656, hlam]
                                          · linarith only [h1491, h1656, hlam]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1491, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1506, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1601, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [h1602, hlam, p1630_0]
                                        · have p1630_0 := h1630c.1
                                          have p1630_1 := h1630c.2.1
                                          have p1630_2 := h1630c.2.2.1
                                          have p1630_3 := h1630c.2.2.2
                                          linarith only [hlam, p1630_0]
                              · linarith only [h1621, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              rcases p1603_3 (m.d 0 1) (by simp) with h1665 | h1665
                              · rcases p1603_3 (m.d 1 2) (by simp) with h1666 | h1666
                                · linarith only [h0, h1666, hlam]
                                · rcases p1603_3 (m.d 1 3) (by simp) with h1668 | h1668
                                  · linarith only [h1, h1668, hlam]
                                  · rcases p1603_3 (m.d 1 4) (by simp) with h1670 | h1670
                                    · linarith only [h1670, h2, hlam]
                                    · linarith only [h1506, h1670, hlam]
                              · linarith only [h1665, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h0, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1492, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1494, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1500, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1, h1034, hc12, hc34, hlam, hphi, ht23, p1603_1]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1502, hlam, p1603_1]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1504, hlam, p1603_1]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h2, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              rcases p1603_3 (m.d 0 1) (by simp) with h1685 | h1685
                              · rcases p1603_3 (m.d 1 2) (by simp) with h1686 | h1686
                                · linarith only [h1494, h1686, hlam]
                                · rcases p1603_3 (m.d 1 3) (by simp) with h1688 | h1688
                                  · linarith only [h1502, h1688, hlam]
                                  · linarith only [h1492, h1688, hlam]
                              · linarith only [h0, h1685, hlam]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, u3ehi1]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1504, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, u3ehi1]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h3, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              rcases p1603_3 (m.d 0 1) (by simp) with h1696 | h1696
                              · rcases p1603_3 (m.d 1 2) (by simp) with h1697 | h1697
                                · linarith only [h1500, h1697, hlam]
                                · rcases p1603_3 (m.d 1 3) (by simp) with h1699 | h1699
                                  · linarith only [h1504, h1699, hlam]
                                  · linarith only [h1492, h1699, hlam]
                              · linarith only [h0, h1696, hlam]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, u3ehi1]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [h1506, hlam, p1603_0]
                            · have p1603_0 := h1603c.1
                              have p1603_1 := h1603c.2.1
                              have p1603_2 := h1603c.2.2.1
                              have p1603_3 := h1603c.2.2.2
                              linarith only [hlam, p1603_0]
                          · linarith only [h1034, h1602, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h1494, h1506, h1601, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1034, h1491, h1502, h1506, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
        · linarith only [h0, h1709, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1711 | h1711
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1712 | h1712
            · linarith only [h0, h1712, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1714 | h1714
              · linarith only [h1, h1034, h1714, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h1709, h1711, h1714, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1717 | h1717
            · linarith only [h0, h1717, h822, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1719 | h1719
              · linarith only [h1, h1034, h1719, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1721 | h1721
                · linarith only [h1, h1034, h1491, h1721, hc45, hlam, hphi, ht34, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1723 | h1723
                  · linarith only [h1034, h1491, h1723, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1725 | h1725
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1726 | h1726
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1727 | h1727
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1728 | h1728
                          · linarith only [h1, h1034, h1491, h1728, hc34, hlam, hphi, u3ehi1]
                          · linarith only [h1, h1034, h1725, h1727, h1728, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h1, h1034, h1725, h1727, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h1, h1034, h1725, h1726, hc35, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1733 | h1733
                      · linarith only [h1725, h1733, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1735 | h1735
                        · linarith only [h1, h1034, h1491, h1725, h1735, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1737 | h1737
                          · linarith only [h1725, h1735, h1737, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h1, h1034, h1737, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h822 | h822
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x1_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h822
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x1_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h822

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1740 | h1740
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1741 | h1741
    · linarith only [h0, h1741, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1743 | h1743
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1744 | h1744
        · linarith only [h1, h1744, h3, hlam]
        · linarith only [h1743, h1744, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1747 | h1747
        · linarith only [h1743, h1747, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1749 | h1749
          · linarith only [h1749, h2, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1751 | h1751
            · linarith only [h0, h1751, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h1740, h1741, h1751, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1754 | h1754
    · linarith only [h1, h1740, h1754, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1756 | h1756
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1757 | h1757
        · linarith only [h1, h1757, h3, hlam]
        · linarith only [h1756, h1757, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1760 | h1760
        · linarith only [h1756, h1760, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1762 | h1762
          · linarith only [h1762, h2, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
            · linarith only [h0, h1764, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1766 | h1766
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1767 | h1767
                · linarith only [h1, h1754, h1764, h1767, h3, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1769 | h1769
                  · linarith only [h1, h1740, h1756, h1767, h1769, h3, hc02, hc25, hlam, hphi]
                  · linarith only [h1764, h1766, h1769, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1772 | h1772
                · linarith only [h0, h1754, h1772, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1774 | h1774
                  · linarith only [h1, h1772, h1774, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1776 | h1776
                    · linarith only [h1760, h1772, h1774, h1776, h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h1774, h1776, h2, h3, hc35, hlam, hphi, u3ehi1]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1779 | h1779
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1780 | h1780
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1781 | h1781
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1782 | h1782
        · linarith only [h0, h1780, h1782, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1784 | h1784
          · linarith only [h1782, h1784, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1786 | h1786
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1787 | h1787
              · linarith only [h0, h1787, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1789 | h1789
                · linarith only [h0, h1780, h1787, h1789, h2, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1780, h1787, h1789, h2, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1780, h1786, h2, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1793 | h1793
        · linarith only [h1779, h1780, h1781, h1793, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1795 | h1795
          · linarith only [h1793, h1795, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1797 | h1797
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1798 | h1798
              · linarith only [h0, h1798, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h1780, h1781, h1798, hc12, hc25, hlam, hphi]
            · linarith only [h1779, h1780, h1781, h1797, h2, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1802 | h1802
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1803 | h1803
        · linarith only [h1, h1803, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1805 | h1805
          · linarith only [h1803, h1805, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1780, h1802, h1805, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1808 | h1808
        · linarith only [h1, h1808, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1810 | h1810
          · linarith only [h1808, h1810, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1812 | h1812
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1813 | h1813
              · linarith only [h0, h1780, h1813, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1815 | h1815
                · linarith only [h0, h1815, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1817 | h1817
                  · linarith only [h1, h1802, h1813, h1815, h1817, h2, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1819 | h1819
                    · linarith only [h1, h1815, h1819, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1, h1819, h2, hc34, hlam, hphi, u3ehi1]
            · linarith only [h1, h1812, h2, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1823 | h1823
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1824 | h1824
      · linarith only [h0, h1779, h1824, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1826 | h1826
        · linarith only [h0, h1823, h1826, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1828 | h1828
          · linarith only [h1826, h1828, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1830 | h1830
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1831 | h1831
              · linarith only [h0, h1831, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h1823, h1824, h1831, hc12, hc25, hlam, hphi]
            · linarith only [h0, h1823, h1830, h2, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1835 | h1835
      · linarith only [h0, h1779, h1835, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1837 | h1837
        · linarith only [h1, h1837, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1839 | h1839
          · linarith only [h1837, h1839, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1841 | h1841
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1842 | h1842
              · linarith only [h0, h1842, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1844 | h1844
                · linarith only [h1, h1842, h1844, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1846 | h1846
                  · linarith only [h1, h1835, h1842, h1844, h1846, h2, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1848 | h1848
                    · linarith only [h1, h1837, h1844, h1848, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h1, h1848, h2, hc34, hlam, hphi, u3ehi1]
            · linarith only [h1, h1841, h2, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2

end R2N4
