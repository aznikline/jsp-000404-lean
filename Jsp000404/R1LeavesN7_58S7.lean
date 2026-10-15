import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h963 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1037 | h1037
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1038 | h1038
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1039 | h1039
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1040 | h1040
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1041 | h1041
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1042 | h1042
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1043 | h1043
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1044 | h1044
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1045 | h1045
                  · linarith only [h1037, h1042, h1045, h963, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1037, h1041, h1042, h1045, h963, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h1037, h1041, h1044, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h1037, h1041, h1042, h1043, h963, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h1037, h1041, h1042, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1051 | h1051
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1052 | h1052
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1054 | h1054
                  · linarith only [h1037, h1041, h1051, h1054, h963, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1056 | h1056
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1057 | h1057
                      · linarith only [h1037, h1041, h1052, h1057, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1059 | h1059
                        · linarith only [h1037, h1041, h1052, h1056, h1059, hlam]
                        · rcases h4bigk with h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1041, h1052, h1056, hc45, hlam, hphi, ht34, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1041, h1056, hc45, hlam, hphi, ht34, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1041, hc45, hlam, hphi, ht34, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1041, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1037, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1037, h1051, h1056, h963, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1037, h1051, h963, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1054, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1038, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1052, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1038, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1057, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1039, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1053, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1056, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1059, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hc45, hlam, hphi, p1061_1, u4ehi0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1053, hc45, hlam, hphi, ht34, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1056, hc45, hlam, hphi, ht34, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1061_1, u3ehi3]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                    · linarith only [h1039, h1041, h1056, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h1039, h1041, h1053, h963, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h1037, h1051, h1052, h963, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h1037, h1051, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h1039, h1040, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1037, h1039, h963, hlam]
    · linarith only [h0, h1037, h1038, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1094 | h1094
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1095 | h1095
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1096 | h1096
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1097 | h1097
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1098 | h1098
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1100 | h1100
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1101 | h1101
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1102 | h1102
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1103 | h1103
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1104 | h1104
                        · linarith only [h1098, h1102, h1104, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1094, h1103, h1104, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1107 | h1107
                        · linarith only [h1102, h1103, h1107, hlam]
                        · rcases h4bigk with h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1037, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            rcases p1109_3 (m.d 0 4) (by simp) with h1112 | h1112
                            · rcases p1109_3 (m.d 1 4) (by simp) with h1113 | h1113
                              · rcases p1109_3 (m.d 2 4) (by simp) with h1114 | h1114
                                · linarith only [h1094, h1114, hlam]
                                · rcases p1109_3 (m.d 3 4) (by simp) with h1116 | h1116
                                  · linarith only [h1095, h1116, hlam]
                                  · rcases p1109_3 (m.d 4 5) (by simp) with h1118 | h1118
                                    · linarith only [h1097, h1118, hlam]
                                    · linarith only [h1103, h1118, hlam]
                              · linarith only [h1099, h1113, hlam]
                            · linarith only [h1094, h1112, hlam]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            rcases p1109_3 (m.d 0 4) (by simp) with h1123 | h1123
                            · rcases p1109_3 (m.d 1 4) (by simp) with h1124 | h1124
                              · rcases p1109_3 (m.d 2 4) (by simp) with h1125 | h1125
                                · linarith only [h1094, h1125, hlam]
                                · linarith only [h1102, h1125, hlam]
                              · linarith only [h1100, h1124, hlam]
                            · linarith only [h1095, h1123, hlam]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1095, h1102, h1103, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi3]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1097, h1100, h1102, h1103, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi3]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            rcases p1109_3 (m.d 0 4) (by simp) with h1133 | h1133
                            · linarith only [h1037, h1133, hlam]
                            · linarith only [h1094, h1133, hlam]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            rcases p1109_3 (m.d 0 4) (by simp) with h1136 | h1136
                            · linarith only [h1037, h1136, hlam]
                            · linarith only [h1095, h1136, hlam]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1098, h1100, h1102, h1103, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi3]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1094, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1099, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1097, h1103, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi3]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1103, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1095, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1100, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1102, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1107, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1097, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1101, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1097, hc04, hlam, hphi, ht0b, ht45, ht5b, p1109_1, u4ehi2]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1037, h1097, h1098, h1100, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi3]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1155 | h1155
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1156 | h1156
                        · rcases h4bigk with h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1037, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1037, h1098, h1100, h1155, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1157_1, u4ehi4]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1037, h1098, h1100, h1102, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1157_1, u3ehi2]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            rcases p1157_3 (m.d 0 4) (by simp) with h1162 | h1162
                            · rcases p1157_3 (m.d 1 4) (by simp) with h1163 | h1163
                              · rcases p1157_3 (m.d 2 4) (by simp) with h1164 | h1164
                                · linarith only [h1094, h1164, hlam]
                                · linarith only [h1155, h1164, hlam]
                              · linarith only [h1101, h1163, hlam]
                            · linarith only [h1162, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1094, h1098, h1100, h1155, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1157_1, u4ehi4]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1098, h1100, h1155, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1157_1, u4ehi4]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1098, h1100, h1102, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1157_1, u3ehi2]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            rcases p1157_3 (m.d 0 4) (by simp) with h1173 | h1173
                            · linarith only [h1037, h1173, hlam]
                            · linarith only [h1097, h1173, hlam]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1094, hlam, p1157_1]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1099, hlam, p1157_1]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1102, hlam, p1157_1]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h0, h1094, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1157_1, u4ehi4]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1095, hlam, p1157_1]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1100, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1095, h1098, h963, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1157_1, u4ehi2]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1095, h1098, h963, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1157_1, u4ehi4]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1097, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1101, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1155, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [h1156, hlam, p1157_0]
                          · have p1157_0 := h1157c.1
                            have p1157_1 := h1157c.2.1
                            have p1157_2 := h1157c.2.2.1
                            have p1157_3 := h1157c.2.2.2
                            linarith only [hlam, p1157_0]
                        · linarith only [h0, h1094, h1155, h1156, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1192 | h1192
                        · linarith only [h1102, h1155, h1192, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1097, h1102, h1192, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1037, h1097, h1101, hlam]
                · linarith only [h1095, h1100, h963, hlam]
              · linarith only [h0, h1094, h1099, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1198 | h1198
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1200 | h1200
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1201 | h1201
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                      · linarith only [h0, h1094, h1098, h1202, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1094, h1097, h1098, h1202, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1094, h1097, h1098, h1201, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1037, h1097, h1200, hlam]
                · linarith only [h0, h1094, h1095, h1097, h1098, h1199, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h0, h1094, h1198, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1209 | h1209
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1210 | h1210
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1211 | h1211
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1212 | h1212
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1213 | h1213
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1214 | h1214
                      · linarith only [h1094, h1097, h1214, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1216 | h1216
                        · linarith only [h1094, h1097, h1213, h1216, hlam]
                        · rcases h4bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1037, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1097, h1212, h1213, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1218_1, u3ehi3]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1097, h1212, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1218_1, u3ehi3]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1097, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            rcases p1218_3 (m.d 0 4) (by simp) with h1224 | h1224
                            · linarith only [h1037, h1224, hlam]
                            · rcases p1218_3 (m.d 1 4) (by simp) with h1226 | h1226
                              · rcases p1218_3 (m.d 2 4) (by simp) with h1227 | h1227
                                · linarith only [h1210, h1227, hlam]
                                · rcases p1218_3 (m.d 3 4) (by simp) with h1229 | h1229
                                  · linarith only [h1211, h1229, hlam]
                                  · rcases p1218_3 (m.d 4 5) (by simp) with h1231 | h1231
                                    · linarith only [h1212, h1231, hlam]
                                    · linarith only [h1097, h1231, hlam]
                              · linarith only [h1037, h1226, hlam]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            rcases p1218_3 (m.d 0 4) (by simp) with h1236 | h1236
                            · linarith only [h1037, h1236, hlam]
                            · linarith only [h1094, h1236, hlam]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            rcases p1218_3 (m.d 0 4) (by simp) with h1239 | h1239
                            · linarith only [h1037, h1239, hlam]
                            · linarith only [h1095, h1239, hlam]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1097, h1209, h1211, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1218_1, u4ehi0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1094, hlam, p1218_1]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1210, hlam, p1218_1]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1094, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1218_1, u3ehi3]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1214, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1095, hlam, p1218_1]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1211, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1213, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1216, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [hc45, hlam, hphi, p1218_1, u4ehi0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1212, hlam, p1218_0]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1209, h1211, h1212, h1213, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1218_1, u3ehi3]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [h1209, h1211, h1212, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1218_1, u3ehi3]
                          · have p1218_0 := h1218c.1
                            have p1218_1 := h1218c.2.1
                            have p1218_2 := h1218c.2.2.1
                            have p1218_3 := h1218c.2.2.2
                            linarith only [hlam, p1218_0]
                    · linarith only [h1095, h1097, h1209, h1211, h1212, h1213, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1259 | h1259
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1260 | h1260
                      · linarith only [h1037, h1212, h1260, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1262 | h1262
                        · linarith only [h1037, h1095, h1212, h1262, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · rcases h4bigk with h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1037, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1037, h1212, hc45, hlam, hphi, p1264_1, u4ehi2]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1037, h1212, hc45, hlam, hphi, ht34, p1264_1, u3ehi3]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1097, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1212, hc45, hlam, hphi, p1264_1, u4ehi0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1212, h1259, hc45, hlam, hphi, ht34, p1264_1, u3ehi3]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1212, hc45, hlam, hphi, ht34, p1264_1, u3ehi3]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1212, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1094, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1210, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1094, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1264_1, u3ehi3]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1260, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1095, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1211, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1259, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1262, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hc45, hlam, hphi, p1264_1, u4ehi0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hc45, hlam, hphi, p1264_1, u4ehi1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1259, hc45, hlam, hphi, ht34, p1264_1, u3ehi3]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1264_1, u3ehi3]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                    · linarith only [h1095, h1097, h1259, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h1095, h1211, h963, hlam]
              · linarith only [h0, h1094, h1210, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1293 | h1293
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1294 | h1294
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1295 | h1295
                  · linarith only [h1097, h1209, h1293, h1295, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1297 | h1297
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1298 | h1298
                      · linarith only [h1037, h1295, h1298, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1300 | h1300
                        · linarith only [h0, h1037, h1094, h1209, h1295, h1297, h1300, hc01, hc23, hlam, hphi, ht12]
                        · rcases h4bigk with h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1037, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1037, h1295, h1297, hc45, hlam, hphi, ht34, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1037, h1295, hc45, hlam, hphi, ht34, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1097, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1295, hc45, hlam, hphi, p1302_1, u4ehi0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1295, h1297, hc45, hlam, hphi, ht34, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1295, hc45, hlam, hphi, ht34, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1295, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1094, hlam, p1302_1]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1293, hlam, p1302_1]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h0, h1094, h1209, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1298, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1095, hlam, p1302_1]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1294, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1297, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1300, hlam, p1302_0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hc45, hlam, hphi, p1302_1, u4ehi0]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hc45, hlam, hphi, p1302_1, u4ehi1]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [h1297, hc45, hlam, hphi, ht34, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1302_1, u3ehi3]
                          · have p1302_0 := h1302c.1
                            have p1302_1 := h1302c.2.1
                            have p1302_2 := h1302c.2.2.1
                            have p1302_3 := h1302c.2.2.2
                            linarith only [hlam, p1302_0]
                    · linarith only [h0, h1209, h1297, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1095, h1097, h1294, h963, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h1094, h1293, hlam]
        · linarith only [h1095, h1096, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1332 | h1332
        · linarith only [h1095, h1332, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1334 | h1334
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1335 | h1335
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1336 | h1336
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1337 | h1337
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1338 | h1338
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
                    · linarith only [h1095, h1335, h1339, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1341 | h1341
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1342 | h1342
                        · rcases h4bigk with h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1037, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1341, hc04, hlam, hphi, ht0b, ht45, ht5b, p1343_1, u4ehi4]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1095, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1095, h1335, h1337, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1343_1, u4ehi4]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1094, h1336, h1341, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1343_1, u4ehi4]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1336, h1341, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1343_1, u4ehi4]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1335, h1337, h1339, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1343_1, u3ehi2]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            rcases p1343_3 (m.d 0 4) (by simp) with h1353 | h1353
                            · linarith only [h1037, h1353, hlam]
                            · linarith only [h1334, h1353, hlam]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1094, hlam, p1343_1]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1336, hlam, p1343_1]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1339, hlam, p1343_1]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1094, hc02, hlam, hphi, ht0b, ht45, ht5b, p1343_1, u4ehi4]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1095, hc34, hlam, hphi, p1343_1, u3ehi0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1337, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1335, h1337, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1343_1, u4ehi2]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1335, h1337, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1343_1, u4ehi4]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1334, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1338, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1341, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [h1342, hlam, p1343_0]
                          · have p1343_0 := h1343c.1
                            have p1343_1 := h1343c.2.1
                            have p1343_2 := h1343c.2.2.1
                            have p1343_3 := h1343c.2.2.2
                            linarith only [hlam, p1343_0]
                        · linarith only [h0, h1094, h1341, h1342, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1095, h1334, h1335, h1337, h1341, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h1095, h1334, h1335, h1337, h1338, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1374 | h1374
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1375 | h1375
                    · linarith only [h1337, h1375, h963, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1377 | h1377
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1378 | h1378
                        · rcases h4bigk with h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1037, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1377, hc04, hlam, hphi, ht0b, ht45, ht5b, p1379_1, u4ehi4]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1095, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            rcases p1379_3 (m.d 0 4) (by simp) with h1384 | h1384
                            · rcases p1379_3 (m.d 1 4) (by simp) with h1385 | h1385
                              · rcases p1379_3 (m.d 2 4) (by simp) with h1386 | h1386
                                · linarith only [h1094, h1386, hlam]
                                · linarith only [h1377, h1386, hlam]
                              · linarith only [h1374, h1385, hlam]
                            · linarith only [h1384, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1094, h1337, h1377, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1379_1, u4ehi4]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1337, h1377, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1379_1, u4ehi4]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1337, hlam, p1379_1]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            rcases p1379_3 (m.d 0 4) (by simp) with h1395 | h1395
                            · linarith only [h1037, h1395, hlam]
                            · linarith only [h1334, h1395, hlam]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1094, hlam, p1379_1]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1336, hlam, p1379_1]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1375, hlam, p1379_1]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h0, h1094, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1379_1, u4ehi4]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1095, hc34, hlam, hphi, p1379_1, u3ehi0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1037, hc01, hc34, hlam, hphi, ht12, ht23, p1379_1]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1375, hc34, hlam, hphi, p1379_1, u3ehi2]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            rcases p1379_3 (m.d 0 4) (by simp) with h1407 | h1407
                            · linarith only [h1095, h1407, hlam]
                            · linarith only [h1334, h1407, hlam]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1334, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1374, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1377, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [h1378, hlam, p1379_0]
                          · have p1379_0 := h1379c.1
                            have p1379_1 := h1379c.2.1
                            have p1379_2 := h1379c.2.2.1
                            have p1379_3 := h1379c.2.2.2
                            linarith only [hlam, p1379_0]
                        · linarith only [h0, h1094, h1377, h1378, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1037, h1334, h1337, h1375, h1377, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h1037, h1334, h1374, hlam]
              · linarith only [h0, h1094, h1336, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1419 | h1419
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1420 | h1420
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1421 | h1421
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1422 | h1422
                    · linarith only [h0, h1094, h1095, h1334, h1335, h1422, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h1335, h1419, h1420, h1422, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h1094, h1095, h1334, h1420, h1421, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h1335, h1419, h1420, hlam]
              · linarith only [h0, h1094, h1419, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1431 | h1431
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h1095, h1428, h1432, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1434 | h1434
                      · linarith only [h1094, h1334, h1434, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1436 | h1436
                        · linarith only [h1094, h1334, h1432, h1436, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1095, h1431, h1436, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1095, h1430, h1431, hc45, hlam, hphi, ht34, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1440 | h1440
                  · linarith only [h1095, h1334, h1430, h1440, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1442 | h1442
                    · linarith only [h1095, h1428, h1442, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1444 | h1444
                      · linarith only [h1094, h1430, h1440, h1444, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1446 | h1446
                        · linarith only [h1037, h1440, h1446, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1095, h1446, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h1094, h1334, h1429, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1450 | h1450
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1451 | h1451
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1452 | h1452
                  · linarith only [h1334, h1428, h1450, h1452, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · linarith only [h1095, h1451, h1452, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h1428, h1450, h1451, hlam]
              · linarith only [h0, h1094, h1450, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1457 | h1457
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1458 | h1458
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1459 | h1459
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1460 | h1460
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1461 | h1461
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1462 | h1462
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1463 | h1463
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1464 | h1464
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1465 | h1465
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1466 | h1466
                        · linarith only [h1460, h1464, h1466, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1094, h1459, h1460, h1464, h1466, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1094, h1459, h1465, hlam]
                    · linarith only [h1094, h1457, h1464, hlam]
                  · linarith only [h1094, h1459, h1461, h1463, hlam]
                · linarith only [h1457, h1462, h963, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1473 | h1473
                · linarith only [h1460, h1461, h1473, hlam]
                · linarith only [h1458, h1473, h963, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1476 | h1476
              · linarith only [h0, h1094, h1460, h1476, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1478 | h1478
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1479 | h1479
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1480 | h1480
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1481 | h1481
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1482 | h1482
                        · rcases h4bigk with h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1037, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1094, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1482, hc04, hlam, hphi, ht0b, ht45, ht5b, p1483_1, u4ehi4]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            rcases p1483_3 (m.d 0 4) (by simp) with h1488 | h1488
                            · rcases p1483_3 (m.d 1 4) (by simp) with h1489 | h1489
                              · rcases p1483_3 (m.d 2 4) (by simp) with h1490 | h1490
                                · rcases p1483_3 (m.d 3 4) (by simp) with h1491 | h1491
                                  · linarith only [h1457, h1491, hlam]
                                  · linarith only [h1482, h1491, hlam]
                                · linarith only [h1481, h1490, hlam]
                              · linarith only [h1479, h1489, hlam]
                            · linarith only [h1488, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1457, h1476, h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1483_1, u4ehi4]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1476, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1476, h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1483_1, u4ehi4]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            rcases p1483_3 (m.d 0 4) (by simp) with h1501 | h1501
                            · linarith only [h1037, h1501, hlam]
                            · linarith only [h1459, h1501, hlam]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1457, h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1483_1, u4ehi4]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1037, h1480, hc01, hc23, hlam, hphi, ht12, p1483_1]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1483_1, u4ehi4]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            rcases p1483_3 (m.d 0 4) (by simp) with h1508 | h1508
                            · linarith only [h1094, h1508, hlam]
                            · linarith only [h1459, h1508, hlam]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1457, hlam, p1483_1]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1478, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1480, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1457, h1460, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1483_1, u4ehi4]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1459, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1479, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1481, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [h1482, hlam, p1483_0]
                          · have p1483_0 := h1483c.1
                            have p1483_1 := h1483c.2.1
                            have p1483_2 := h1483c.2.2.1
                            have p1483_3 := h1483c.2.2.2
                            linarith only [hlam, p1483_0]
                        · rcases h4bigk with h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1037, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1094, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            rcases p1521_3 (m.d 0 4) (by simp) with h1525 | h1525
                            · rcases p1521_3 (m.d 1 4) (by simp) with h1526 | h1526
                              · rcases p1521_3 (m.d 2 4) (by simp) with h1527 | h1527
                                · rcases p1521_3 (m.d 3 4) (by simp) with h1528 | h1528
                                  · linarith only [h1457, h1528, hlam]
                                  · rcases p1521_3 (m.d 4 5) (by simp) with h1530 | h1530
                                    · linarith only [h1459, h1530, hlam]
                                    · linarith only [h1482, h1530, hlam]
                                · linarith only [h1480, h1527, hlam]
                              · linarith only [h1478, h1526, hlam]
                            · linarith only [h1457, h1525, hlam]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1457, h1460, h1482, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1521_1, u4ehi3]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1459, h1476, h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1476, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            rcases p1521_3 (m.d 0 4) (by simp) with h1540 | h1540
                            · linarith only [h1037, h1540, hlam]
                            · linarith only [h1457, h1540, hlam]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1476, h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1459, h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1037, h1480, hc01, hc23, hlam, hphi, ht12, p1521_1]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            rcases p1521_3 (m.d 0 4) (by simp) with h1547 | h1547
                            · linarith only [h1094, h1547, hlam]
                            · linarith only [h1457, h1547, hlam]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1480, h1482, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1457, hlam, p1521_1]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1478, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1480, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1482, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1459, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1479, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1481, hlam, p1521_0]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [h1459, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1521_1, u3ehi3]
                          · have p1521_0 := h1521c.1
                            have p1521_1 := h1521c.2.1
                            have p1521_2 := h1521c.2.2.1
                            have p1521_3 := h1521c.2.2.2
                            linarith only [hlam, p1521_0]
                      · linarith only [h1457, h1459, h1460, h1476, h1481, h963, hc12, hc23, hlam, hphi]
                    · linarith only [h1457, h1460, h1480, h963, hlam]
                  · linarith only [h1037, h1459, h1479, hlam]
                · linarith only [h1457, h1478, h963, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1565 | h1565
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1566 | h1566
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1567 | h1567
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1568 | h1568
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1569 | h1569
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1570 | h1570
                      · linarith only [h1459, h1566, h1570, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h1094, h1565, h1567, h1568, h1570, hc01, hc12, hlam, hphi]
                    · linarith only [h1457, h1459, h1565, h1567, h1568, h1569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1574 | h1574
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1575 | h1575
                      · linarith only [h1566, h1568, h1575, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1577 | h1577
                        · linarith only [h1094, h1457, h1566, h1568, h1577, hlam]
                        · rcases h4bigk with h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1037, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1094, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1094, h1566, h1568, hc45, hlam, hphi, p1579_1, u4ehi3]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1459, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1568, hc45, hlam, hphi, p1579_1, u4ehi0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1568, hc45, hlam, hphi, p1579_1, u4ehi2]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1568, hc45, hlam, hphi, ht34, p1579_1, u3ehi3]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1568, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1457, h1566, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1579_1, u3ehi3]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1566, hlam, p1579_1]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1566, h1568, hc45, hlam, hphi, ht34, p1579_1, u3ehi3]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1575, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1457, hlam, p1579_1]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1567, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1574, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1577, hlam, p1579_0]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h1457, hc45, hlam, hphi, ht34, p1579_1, u3ehi3]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hc45, hlam, hphi, p1579_1, u4ehi1]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [h0, h1094, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1579_1]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1579_1, u3ehi3]
                          · have p1579_0 := h1579c.1
                            have p1579_1 := h1579c.2.1
                            have p1579_2 := h1579c.2.2.1
                            have p1579_3 := h1579c.2.2.2
                            linarith only [hlam, p1579_0]
                    · linarith only [h1457, h1459, h1574, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h1457, h1567, h963, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1607 | h1607
                · linarith only [h1565, h1566, h1607, hlam]
                · linarith only [h1457, h1607, h963, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1610 | h1610
              · linarith only [h0, h1094, h1565, h1610, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1612 | h1612
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1613 | h1613
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1614 | h1614
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1615 | h1615
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1616 | h1616
                        · linarith only [h1457, h1459, h1616, hlam]
                        · rcases h4bigk with h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1037, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1094, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1459, h1613, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi3]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1459, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            rcases p1618_3 (m.d 0 4) (by simp) with h1624 | h1624
                            · linarith only [h1037, h1624, hlam]
                            · rcases p1618_3 (m.d 1 4) (by simp) with h1626 | h1626
                              · rcases p1618_3 (m.d 2 4) (by simp) with h1627 | h1627
                                · rcases p1618_3 (m.d 3 4) (by simp) with h1628 | h1628
                                  · linarith only [h1612, h1628, hlam]
                                  · rcases p1618_3 (m.d 4 5) (by simp) with h1630 | h1630
                                    · linarith only [h1613, h1630, hlam]
                                    · linarith only [h1459, h1630, hlam]
                                · linarith only [h1094, h1627, hlam]
                              · linarith only [h1037, h1626, hlam]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1610, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            rcases p1618_3 (m.d 0 4) (by simp) with h1637 | h1637
                            · linarith only [h1037, h1637, hlam]
                            · linarith only [h1457, h1637, hlam]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1459, h1610, h1614, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u4ehi0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            rcases p1618_3 (m.d 0 4) (by simp) with h1641 | h1641
                            · linarith only [h1094, h1641, hlam]
                            · rcases p1618_3 (m.d 1 4) (by simp) with h1643 | h1643
                              · linarith only [h1610, h1643, hlam]
                              · linarith only [h1037, h1643, hlam]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1037, h1614, hc01, hc23, hlam, hphi, ht12, p1618_1]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            rcases p1618_3 (m.d 0 4) (by simp) with h1648 | h1648
                            · linarith only [h1094, h1648, hlam]
                            · linarith only [h1457, h1648, hlam]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1457, h1459, h1614, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1618_1, u3ehi3]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1457, hlam, p1618_1]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1612, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1614, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1616, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1457, h1613, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi3]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1613, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1615, hlam, p1618_0]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [h1610, h1613, h1614, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1618_1, u3ehi3]
                          · have p1618_0 := h1618c.1
                            have p1618_1 := h1618c.2.1
                            have p1618_2 := h1618c.2.2.1
                            have p1618_3 := h1618c.2.2.2
                            linarith only [hlam, p1618_0]
                      · linarith only [h1610, h1613, h1615, hlam]
                    · linarith only [h1458, h1565, h1614, h963, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1664 | h1664
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1665 | h1665
                      · linarith only [h0, h1610, h1613, h1664, h1665, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1610, h1665, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1037, h1457, h1613, h1664, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h1457, h1612, h963, hlam]
        · linarith only [h1457, h1458, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1671 | h1671
        · linarith only [h1457, h1671, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1673 | h1673
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1674 | h1674
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1675 | h1675
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1676 | h1676
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1677 | h1677
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1678 | h1678
                    · linarith only [h1457, h1674, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1680 | h1680
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1681 | h1681
                        · rcases h4bigk with h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1037, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1094, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1457, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1094, h1675, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1673, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1094, h1673, h1675, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1674, h1676, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1682_1, u3ehi2]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            rcases p1682_3 (m.d 0 4) (by simp) with h1692 | h1692
                            · linarith only [h1037, h1692, hlam]
                            · linarith only [h1673, h1692, hlam]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1673, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1675, hlam, p1682_1]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1678, hlam, p1682_1]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1674, h1676, h1678, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1673, h1674, h1676, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1676, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1674, h1676, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi2]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1674, h1676, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1, u4ehi4]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1673, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1677, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1680, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [h1681, hlam, p1682_0]
                          · have p1682_0 := h1682c.1
                            have p1682_1 := h1682c.2.1
                            have p1682_2 := h1682c.2.2.1
                            have p1682_3 := h1682c.2.2.2
                            linarith only [hlam, p1682_0]
                        · linarith only [h1457, h1673, h1681, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1094, h1673, h1680, hlam]
                  · linarith only [h1037, h1094, h1673, h1677, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1713 | h1713
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1714 | h1714
                    · linarith only [h1676, h1714, h963, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1716 | h1716
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1717 | h1717
                        · rcases h4bigk with h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1037, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1094, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1457, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1094, h1675, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1718_1, u4ehi4]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1457, h1676, hc34, hlam, hphi, p1718_1, u3ehi0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h0, h1094, h1676, hc01, hc34, hlam, hphi, ht12, ht23, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1676, hlam, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            rcases p1718_3 (m.d 0 4) (by simp) with h1728 | h1728
                            · linarith only [h1037, h1728, hlam]
                            · linarith only [h1673, h1728, hlam]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1673, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1718_1, u4ehi4]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1675, hlam, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1714, hlam, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1675, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1718_1, u4ehi4]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1673, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1718_1, u4ehi4]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1037, hc01, hc34, hlam, hphi, ht12, ht23, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1094, h1673, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1718_1, u4ehi4]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            rcases p1718_3 (m.d 0 4) (by simp) with h1740 | h1740
                            · linarith only [h1457, h1740, hlam]
                            · linarith only [h1673, h1740, hlam]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1673, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1713, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1716, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1717, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                        · linarith only [h1673, h1676, h1717, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1094, h1673, h1716, hlam]
                  · linarith only [h1094, h1673, h1675, h1713, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1751 | h1751
                · linarith only [h1457, h1673, h1674, h1675, h1751, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1753 | h1753
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1754 | h1754
                    · linarith only [h1674, h1675, h1751, h1754, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h1674, h1675, h1754, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h1673, h1674, h1675, h1753, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1758 | h1758
              · linarith only [h0, h1094, h1674, h1758, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1760 | h1760
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1761 | h1761
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1762 | h1762
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1763 | h1763
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1764 | h1764
                        · rcases h4bigk with h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1037, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1094, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1457, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1457, h1674, h1760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1765_1, u4ehi4]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1673, h1674, h1760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1765_1, u4ehi4]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1758, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1457, h1674, h1760, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1765_1, u3ehi0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            rcases p1765_3 (m.d 0 4) (by simp) with h1775 | h1775
                            · linarith only [h1037, h1775, hlam]
                            · linarith only [h1673, h1775, hlam]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1673, h1762, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1765_1, u4ehi4]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1037, h1762, hc01, hc23, hlam, hphi, ht12, p1765_1]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1671, h1762, h1764, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1765_1, u3ehi0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            rcases p1765_3 (m.d 0 4) (by simp) with h1782 | h1782
                            · linarith only [h1094, h1782, hlam]
                            · linarith only [h1673, h1782, hlam]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1673, h1760, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1765_1, u4ehi4]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1760, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1762, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1674, h1760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1765_1, u4ehi4]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1673, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1761, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1763, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [h1764, hlam, p1765_0]
                          · have p1765_0 := h1765c.1
                            have p1765_1 := h1765c.2.1
                            have p1765_2 := h1765c.2.2.1
                            have p1765_3 := h1765c.2.2.2
                            linarith only [hlam, p1765_0]
                        · linarith only [h1457, h1673, h1764, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1457, h1673, h1758, h1763, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1674, h1760, h1762, hlam]
                  · linarith only [h1457, h1673, h1674, h1760, h1761, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1799 | h1799
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1800 | h1800
                    · linarith only [h1760, h1800, h963, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h1674, h1800, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1037, h1673, h1799, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1804 | h1804
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1805 | h1805
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1806 | h1806
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1807 | h1807
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1808 | h1808
                    · linarith only [h1457, h1804, h1808, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1810 | h1810
                      · linarith only [h1457, h1673, h1805, h1810, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1094, h1806, h1807, h1810, hc01, hc13, hlam, hphi]
                  · linarith only [h1457, h1806, h1807, hc45, hlam, hphi, ht34, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1814 | h1814
                  · linarith only [h1457, h1673, h1806, h1814, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1816 | h1816
                    · linarith only [h1457, h1804, h1816, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1818 | h1818
                      · linarith only [h1805, h1814, h1818, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1820 | h1820
                        · linarith only [h0, h1094, h1805, h1814, h1820, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1457, h1820, hc45, hlam, hphi, ht34, u3ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1823 | h1823
                · linarith only [h1457, h1804, h1805, h1823, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1825 | h1825
                  · linarith only [h1457, h1673, h1823, h1825, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h1804, h1805, h1825, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1828 | h1828
              · linarith only [h0, h1094, h1804, h1828, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1830 | h1830
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1831 | h1831
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1832 | h1832
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1833 | h1833
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1834 | h1834
                        · linarith only [h1457, h1673, h1834, hc34, hlam, hphi, u3ehi0]
                        · linarith only [h1457, h1831, h1834, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1828, h1831, h1833, hlam]
                    · linarith only [h0, h1457, h1673, h1804, h1828, h1831, h1832, hc01, hc24, hc34, hlam, hphi, ht12, u3ehi0]
                  · linarith only [h1457, h1830, h1831, hc45, hlam, hphi, ht34, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1840 | h1840
                  · linarith only [h1457, h1673, h1830, h1840, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h0, h1804, h1830, h1842, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h1804, h1842, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h963 | h963
  · exact r1l7_13_24_L_R_M_IR_x1_x0 m hb3 hb4 h0 h963
  · exact r1l7_13_24_L_R_M_IR_x1_x1 m hb3 hb4 h0 h963

end R2N4
