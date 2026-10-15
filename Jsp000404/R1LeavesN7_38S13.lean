import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1030 | h1030
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1031 | h1031
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1032 | h1032
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1033 | h1033
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1034 | h1034
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1035 | h1035
            · linarith only [h0, h1030, h1035, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1037 | h1037
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1038 | h1038
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1039 | h1039
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1040 | h1040
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1041 | h1041
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1042 | h1042
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1043 | h1043
                          · linarith only [h0, h1037, h1043, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h1030, h1034, h1041, h1043, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h1042, h4, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h1041, h4, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1030, h1034, h1040, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h1033, h1035, h1039, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h1031, h1037, h1038, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1030, h1037, h4, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1052 | h1052
            · linarith only [h0, h1030, h1052, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1054 | h1054
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1056 | h1056
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1057 | h1057
                    · linarith only [h1034, h1057, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1059 | h1059
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1060 | h1060
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1061 | h1061
                          · linarith only [h0, h1034, h1054, h1061, h2, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
                            · linarith only [h1030, h1034, h1059, h1063, h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · rcases h0bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h0, h1055, h1059, h1061, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1065_1]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h0, h1055, h1059, h1061, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1065_1]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                rcases p1065_3 (m.d 0 1) (by simp) with h1069 | h1069
                                · rcases p1065_3 (m.d 0 2) (by simp) with h1070 | h1070
                                  · linarith only [h0, h1070, hlam]
                                  · linarith only [h1030, h1070, hlam]
                                · linarith only [h1069, h2, hlam]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                rcases p1065_3 (m.d 0 1) (by simp) with h1074 | h1074
                                · rcases p1065_3 (m.d 0 2) (by simp) with h1075 | h1075
                                  · linarith only [h0, h1075, hlam]
                                  · linarith only [h1031, h1075, hlam]
                                · linarith only [h1074, h3, hlam]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h0, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h4, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1065_1, u3elo2]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1030, h1034, h1059, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1065_1, u3elo2]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1, hlam, p1065_1]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h0, h1055, hc03, hc25, hlam, hphi, ht0b, ht5b, p1065_1]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1030, h1059, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1065_1, u3elo2]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1030, h1034, h1059, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1065_1, u3elo2]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h2, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1030, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1032, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1034, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h3, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1031, hlam, p1065_1]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1033, hlam, p1065_0]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [h1030, h1031, h1059, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1065_1, u3elo2]
                              · have p1065_0 := h1065c.1
                                have p1065_1 := h1065c.2.1
                                have p1065_2 := h1065c.2.2.1
                                have p1065_3 := h1065c.2.2.2
                                linarith only [hlam, p1065_0]
                        · linarith only [h1060, h4, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h0, h1054, h1059, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h1031, h1033, h1056, h4, hc13, hlam, hphi, u3elo2]
                · linarith only [h1031, h1054, h1055, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1030, h1054, h4, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h1031, h1033, h4, hlam]
      · linarith only [h1030, h1032, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1106 | h1106
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1107 | h1107
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1108 | h1108
          · linarith only [h1030, h1031, h1108, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1110 | h1110
            · linarith only [h0, h1110, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
                · linarith only [h1031, h1110, h1113, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                    · linarith only [h0, h1108, h1112, h1116, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1119 | h1119
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1120 | h1120
                          · linarith only [h1030, h1031, h1108, h1120, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1122 | h1122
                            · linarith only [h1031, h1120, h1122, hc02, hlam, hphi, ht23, u3elo3]
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
                                linarith only [h0, h1112, h1118, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h0, h1031, h1107, h1112, h1118, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                rcases p1124_3 (m.d 0 1) (by simp) with h1128 | h1128
                                · rcases p1124_3 (m.d 0 2) (by simp) with h1129 | h1129
                                  · linarith only [h0, h1129, hlam]
                                  · linarith only [h1030, h1129, hlam]
                                · linarith only [h1128, h2, hlam]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h0, h1031, h1112, h1118, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1124_1]
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
                                linarith only [h1031, h1112, h1118, h1119, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1031, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1, hlam, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hc02, hlam, hphi, ht23, p1124_1, u3elo0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1112, h1118, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1124_1, u3elo2]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h0, h1031, h1112, h1118, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1124_1, u3elo2]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h2, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1030, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1106, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1108, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h3, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h0, h1112, h1118, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1107, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1031, h1112, h1118, h1119, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1124_1, u3elo2]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                        · linarith only [h1, h1115, h1119, h4, hlam]
                      · linarith only [h0, h1112, h1118, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h1107, h1115, hc13, hlam, hphi, u3elo0]
              · linarith only [h1030, h1112, h4, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
          · linarith only [h1030, h1031, h1158, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1160 | h1160
            · linarith only [h0, h1107, h1160, h4, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1162 | h1162
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1163 | h1163
                · linarith only [h0, h1031, h1163, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h0, h1107, h1162, h1165, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1167 | h1167
                    · linarith only [h1158, h1167, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
                        · linarith only [h0, h1107, h1162, h1169, h1170, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h0, h1162, h1169, h1170, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1162, h1169, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h1030, h1107, h1162, h4, hc12, hlam, hphi, ht23, u3elo4]
      · linarith only [h1030, h1106, h4, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1176 | h1176
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1177 | h1177
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1178 | h1178
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1179 | h1179
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1180 | h1180
            · linarith only [h0, h1176, h1180, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1182 | h1182
              · linarith only [h0, h1030, h1182, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1184 | h1184
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1185 | h1185
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1186 | h1186
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1187 | h1187
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1188 | h1188
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1189 | h1189
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1190 | h1190
                            · rcases h0bigk with h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, h1184, h1188, h1190, hc01, hc45, hlam, hphi, ht0b, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1177, h1190, hc01, hc45, hlam, hphi, ht0b, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, h1030, h1184, h1188, h1190, hc01, hc45, hlam, hphi, ht0b, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1196 | h1196
                                · rcases p1191_3 (m.d 0 2) (by simp) with h1197 | h1197
                                  · linarith only [h0, h1197, hlam]
                                  · linarith only [h1176, h1197, hlam]
                                · linarith only [h1196, h3, hlam]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h4, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1030, hlam, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1030, h1187, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1, hlam, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h4, hc02, hlam, hphi, ht23, p1191_1, u3elo2]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, h1030, h1184, h1188, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1191_1, u3elo2]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1176, h1188, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1191_1, u3elo2]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h2, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, h1184, h1188, hc04, hc35, hlam, hphi, ht0b, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1177, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1030, h1176, h1187, h1188, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1191_1, u3elo2]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h3, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1176, hlam, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1178, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1179, hlam, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                            · linarith only [h0, h1184, h1189, h1190, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h1030, h1179, h1189, hlam]
                        · linarith only [h1030, h1187, h1188, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h0, h1184, h1187, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1177, h1179, h1182, h1184, h1186, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · linarith only [h1178, h1185, h4, hc13, hlam, hphi, u3elo2]
                · linarith only [h1176, h1184, h4, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h1030, h1176, h1179, hlam]
        · linarith only [h1030, h1176, h1177, h1178, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1230 | h1230
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1231 | h1231
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1232 | h1232
            · linarith only [h0, h1232, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1234 | h1234
              · linarith only [h1030, h1232, h1234, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1238 | h1238
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1239 | h1239
                      · linarith only [h0, h1177, h1236, h1239, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h0, h1236, h1239, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1177, h1231, h1234, h1236, h1238, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h1230, h1237, hc13, hlam, hphi, u3elo0]
                · linarith only [h1176, h1177, h1236, h4, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h1030, h1176, h1231, hlam]
        · linarith only [h1176, h1230, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1247 | h1247
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1248 | h1248
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1249 | h1249
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1250 | h1250
            · linarith only [h0, h1250, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1252 | h1252
              · linarith only [h1030, h1250, h1252, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1254 | h1254
                · linarith only [h0, h1176, h1254, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1256 | h1256
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1257 | h1257
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1258 | h1258
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1259 | h1259
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1260 | h1260
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1261 | h1261
                            · rcases h0bigk with h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c | h1262c
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                rcases p1262_3 (m.d 0 1) (by simp) with h1264 | h1264
                                · rcases p1262_3 (m.d 0 2) (by simp) with h1265 | h1265
                                  · linarith only [h0, h1265, hlam]
                                  · rcases p1262_3 (m.d 0 3) (by simp) with h1267 | h1267
                                    · linarith only [h1, h1267, hlam]
                                    · linarith only [h1267, h4, hlam]
                                · linarith only [h0, h1264, hlam]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1247, h1261, hc01, hc45, hlam, hphi, ht0b, ht5b, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1257, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                rcases p1262_3 (m.d 0 1) (by simp) with h1273 | h1273
                                · rcases p1262_3 (m.d 0 2) (by simp) with h1274 | h1274
                                  · linarith only [h0, h1274, hlam]
                                  · rcases p1262_3 (m.d 0 3) (by simp) with h1276 | h1276
                                    · linarith only [h1, h1276, hlam]
                                    · linarith only [h1248, h1276, hlam]
                                · linarith only [h1273, h3, hlam]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h0, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h4, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1030, hlam, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1176, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1, hlam, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h0, h4, hc12, hc23, hlam, hphi, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1257, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1262_1, u3elo2]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h0, h1176, h4, hc12, hlam, hphi, ht23, p1262_1, u3elo2]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h2, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h0, h1030, hc12, hc24, hlam, hphi, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1247, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h0, h1176, h1247, h4, hc12, hlam, hphi, ht23, p1262_1, u3elo2]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h3, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h0, h1176, hc12, hc25, hlam, hphi, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1248, hlam, p1262_0]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [h1249, hlam, p1262_1]
                              · have p1262_0 := h1262c.1
                                have p1262_1 := h1262c.2.1
                                have p1262_2 := h1262c.2.2.1
                                have p1262_3 := h1262c.2.2.2
                                linarith only [hlam, p1262_0]
                            · rcases h0bigk with h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                rcases p1300_3 (m.d 0 1) (by simp) with h1302 | h1302
                                · rcases p1300_3 (m.d 0 2) (by simp) with h1303 | h1303
                                  · linarith only [h0, h1303, hlam]
                                  · rcases p1300_3 (m.d 0 3) (by simp) with h1305 | h1305
                                    · linarith only [h1, h1305, hlam]
                                    · linarith only [h1305, h4, hlam]
                                · linarith only [h0, h1302, hlam]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1247, h1257, h1261, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1257, h1261, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1257, h1261, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h0, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h4, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1030, hlam, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1176, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1, hlam, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, p1300_1, u3elo0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1257, h1261, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1300_1, u3elo2]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1257, h1261, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1300_1, u3elo2]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h2, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h0, h1030, h1258, hc12, hlam, hphi, ht23, p1300_1, u3elo2]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1247, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1030, h1257, h1258, h1261, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1300_1, u3elo2]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h3, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h0, h1176, h1258, h1260, hc12, hlam, hphi, ht23, p1300_1, u3elo2]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1248, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1249, hlam, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                          · linarith only [h1030, h1257, h1260, h2, hlam]
                        · linarith only [h0, h1259, h4, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h0, h1258, h4, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1247, h1249, h1252, h1257, hc12, hlam, hphi, ht23, u3elo0]
                  · linarith only [h1248, h1256, h4, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1337 | h1337
            · linarith only [h0, h1337, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1339 | h1339
              · linarith only [h1030, h1337, h1339, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1341 | h1341
                · linarith only [h0, h1176, h1341, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1343 | h1343
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1344 | h1344
                    · linarith only [h1249, h1344, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1348 | h1348
                          · linarith only [h0, h1030, h1249, h1346, h1348, hc12, hlam, hphi, ht23, u3elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1350 | h1350
                            · linarith only [h1247, h1348, h1350, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases h0bigk with h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                rcases p1352_3 (m.d 0 1) (by simp) with h1354 | h1354
                                · rcases p1352_3 (m.d 0 2) (by simp) with h1355 | h1355
                                  · linarith only [h0, h1355, hlam]
                                  · rcases p1352_3 (m.d 0 3) (by simp) with h1357 | h1357
                                    · linarith only [h1, h1357, hlam]
                                    · linarith only [h1357, h4, hlam]
                                · linarith only [h0, h1354, hlam]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1, h1343, h1350, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1352_1]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                rcases p1352_3 (m.d 0 1) (by simp) with h1362 | h1362
                                · rcases p1352_3 (m.d 0 2) (by simp) with h1363 | h1363
                                  · linarith only [h0, h1363, hlam]
                                  · rcases p1352_3 (m.d 0 3) (by simp) with h1365 | h1365
                                    · linarith only [h1, h1365, hlam]
                                    · linarith only [h1247, h1365, hlam]
                                · linarith only [h1362, h2, hlam]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                rcases p1352_3 (m.d 0 1) (by simp) with h1369 | h1369
                                · rcases p1352_3 (m.d 0 2) (by simp) with h1370 | h1370
                                  · linarith only [h0, h1370, hlam]
                                  · rcases p1352_3 (m.d 0 3) (by simp) with h1372 | h1372
                                    · linarith only [h1, h1372, hlam]
                                    · linarith only [h1248, h1372, hlam]
                                · linarith only [h1369, h3, hlam]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h0, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h4, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1030, hlam, p1352_1]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1176, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1, hlam, p1352_1]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, p1352_1, u3elo0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h0, h1030, h4, hc12, hlam, hphi, ht23, p1352_1, u3elo2]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h0, h1030, h1249, h4, hc12, hlam, hphi, ht23, p1352_1, u3elo2]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h2, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h0, h1030, hc12, hc24, hlam, hphi, p1352_1]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1247, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1249, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h3, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h0, h1176, hc12, hc25, hlam, hphi, p1352_1]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1248, hlam, p1352_0]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [h1248, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1352_1, u3elo2]
                              · have p1352_0 := h1352c.1
                                have p1352_1 := h1352c.2.1
                                have p1352_2 := h1352c.2.2.1
                                have p1352_3 := h1352c.2.2.2
                                linarith only [hlam, p1352_0]
                        · linarith only [h1343, h1347, h4, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h1346, h4, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1248, h1343, h4, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1399 | h1399
          · linarith only [h1247, h1248, h1399, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1401 | h1401
            · linarith only [h0, h1401, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1403 | h1403
              · linarith only [h1030, h1401, h1403, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1405 | h1405
                · linarith only [h0, h1176, h1405, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1407 | h1407
                  · linarith only [h1, h1248, h1407, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1409 | h1409
                    · linarith only [h1399, h1409, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1411 | h1411
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1412 | h1412
                        · linarith only [h1248, h1412, hc03, hlam, hphi, u3elo2]
                        · linarith only [h0, h1412, h4, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h0, h1411, h4, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1416 | h1416
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1417 | h1417
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1418 | h1418
            · linarith only [h0, h1418, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1420 | h1420
              · linarith only [h0, h1030, h1420, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1422 | h1422
                · linarith only [h0, h1176, h1422, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1424 | h1424
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1425 | h1425
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1426 | h1426
                      · linarith only [h1176, h1247, h1416, h1426, hc02, hlam, hphi, ht23, u3elo2]
                      · linarith only [h1426, h4, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1247, h1416, h1417, h1420, h1425, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1247, h1416, h1418, h1424, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h1247, h1416, h1417, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1432 | h1432
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1433 | h1433
            · linarith only [h0, h1433, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1435 | h1435
              · linarith only [h0, h1030, h1435, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1437 | h1437
                · linarith only [h0, h1176, h1437, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1439 | h1439
                  · linarith only [h1416, h1439, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1441 | h1441
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1442 | h1442
                      · linarith only [h0, h1247, h1442, h4, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h0, h1442, h4, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1247, h1432, h1435, h1441, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
            · linarith only [h0, h1446, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1448 | h1448
              · linarith only [h0, h1030, h1448, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1450 | h1450
                · linarith only [h0, h1176, h1450, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1452 | h1452
                  · linarith only [h1416, h1452, h4, hc02, hlam, hphi, ht23, u3elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1454 | h1454
                    · linarith only [h1432, h1454, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1456 | h1456
                      · linarith only [h0, h1247, h1456, h4, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h0, h1456, h4, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1459 | h1459
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1460 | h1460
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1461 | h1461
      · linarith only [h0, h1461, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1463 | h1463
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1464 | h1464
          · linarith only [h0, h1459, h1464, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1466 | h1466
            · linarith only [h0, h1459, h1463, h1466, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1468 | h1468
              · linarith only [h0, h1464, h1468, h3, hc23, hlam, hphi, u3elo4]
              · linarith only [h1459, h1461, h1468, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1471 | h1471
          · linarith only [h1, h1463, h1471, h3, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1473 | h1473
            · linarith only [h0, h1460, h1473, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1475 | h1475
              · linarith only [h0, h1471, h1475, h3, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h1459, h1471, h1475, h3, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1478 | h1478
      · linarith only [h1460, h1478, h2, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1480 | h1480
        · linarith only [h1459, h1460, h1480, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1482 | h1482
          · linarith only [h1, h1480, h1482, h3, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1484 | h1484
            · linarith only [h1484, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1486 | h1486
              · linarith only [h0, h1482, h1486, h3, hc23, hlam, hphi, u3elo4]
              · linarith only [h1459, h1460, h1484, h1486, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1489 | h1489
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1490 | h1490
      · linarith only [h0, h1490, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1492 | h1492
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
          · linarith only [h1, h1493, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1495 | h1495
            · linarith only [h0, h1459, h1489, h1493, h1495, h3, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1497 | h1497
              · linarith only [h0, h1459, h1493, h1497, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1499 | h1499
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1500 | h1500
                  · linarith only [h0, h1490, h1500, h3, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1502 | h1502
                    · linarith only [h1, h1492, h1493, h1502, h3, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1, h1497, h1499, h1502, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h1459, h1489, h1493, h1499, hc12, hlam, hphi, ht23, u3elo4]
        · linarith only [h1459, h1489, h1492, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1507 | h1507
      · linarith only [h1, h1459, h1507, h3, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1509 | h1509
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1510 | h1510
          · linarith only [h1, h1510, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1512 | h1512
            · linarith only [h0, h1509, h1510, h1512, h3, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1514 | h1514
              · linarith only [h0, h1489, h1509, h1510, h1514, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1516 | h1516
                · linarith only [h0, h1489, h1516, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1518 | h1518
                  · linarith only [h1, h1507, h1514, h1518, h3, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1520 | h1520
                    · linarith only [h1, h1489, h1509, h1510, h1520, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1520, h3, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1523 | h1523
          · linarith only [h1, h1509, h1523, h3, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1525 | h1525
            · linarith only [h1525, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1527 | h1527
              · linarith only [h0, h1459, h1527, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1529 | h1529
                · linarith only [h0, h1489, h1529, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1531 | h1531
                  · linarith only [h0, h1507, h1531, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1533 | h1533
                    · linarith only [h1, h1523, h1533, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1, h1527, h1533, h3, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1536 | h1536
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1537 | h1537
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1538 | h1538
      · linarith only [h0, h1538, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1540 | h1540
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1541 | h1541
          · linarith only [h1, h1541, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1543 | h1543
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1544 | h1544
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1545 | h1545
                · linarith only [h0, h1541, h1545, h2, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1537, h1541, h1545, h2, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h0, h1537, h1541, h1543, h1544, h2, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1549 | h1549
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1550 | h1550
                · linarith only [h0, h1541, h1550, h2, hc23, hlam, hphi, u3elo3]
                · linarith only [h1537, h1538, h1550, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1540, h1549, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1554 | h1554
          · linarith only [h1, h1554, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1556 | h1556
            · linarith only [h1537, h1540, h1556, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1558 | h1558
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1559 | h1559
                · linarith only [h0, h1554, h1559, h2, hc23, hlam, hphi, u3elo3]
                · linarith only [h1537, h1540, h1559, hc12, hc25, hlam, hphi]
              · linarith only [h1536, h1558, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1563 | h1563
      · linarith only [h0, h1563, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1565 | h1565
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1566 | h1566
          · linarith only [h1, h1566, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1568 | h1568
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1569 | h1569
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1570 | h1570
                · linarith only [h0, h1537, h1566, h1570, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1572 | h1572
                  · linarith only [h1, h1563, h1570, h1572, h2, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1574 | h1574
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1575 | h1575
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1576 | h1576
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1577 | h1577
                          · linarith only [h1537, h1566, h1577, hc02, hlam, hphi, ht23, u3elo2]
                          · linarith only [h1537, h1577, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h1, h1565, h1569, h1570, h1574, h1576, h2, hc02, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1566, h1568, h1570, h1574, h1575, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1537, h1565, h1566, h1574, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1, h1537, h1565, h1566, h1569, h2, hc13, hlam, hphi, u3elo3]
            · linarith only [h1537, h1565, h1568, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1585 | h1585
          · linarith only [h1, h1585, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1587 | h1587
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1588 | h1588
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1589 | h1589
                · linarith only [h0, h1565, h1585, h1587, h1589, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1591 | h1591
                  · linarith only [h0, h1563, h1591, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1593 | h1593
                    · linarith only [h0, h1565, h1593, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1595 | h1595
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1596 | h1596
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1597 | h1597
                          · linarith only [h1, h1585, h1593, h1595, h1597, h2, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h1537, h1597, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h1, h1595, h1596, h2, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h1587, h1595, hc13, hlam, hphi, u3elo0]
              · linarith only [h1536, h1588, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1603 | h1603
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1604 | h1604
                · linarith only [h0, h1537, h1604, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1606 | h1606
                  · linarith only [h0, h1563, h1606, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1608 | h1608
                    · linarith only [h0, h1565, h1608, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1610 | h1610
                      · linarith only [h1, h1587, h1610, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1612 | h1612
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1613 | h1613
                          · linarith only [h0, h1585, h1613, h2, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h0, h1537, h1613, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h1536, h1604, h1610, h1612, h2, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h1536, h1603, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1618 | h1618
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1619 | h1619
      · linarith only [h0, h1619, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1621 | h1621
        · linarith only [h0, h1536, h1621, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1623 | h1623
          · linarith only [h1, h1623, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1625 | h1625
            · linarith only [h0, h1536, h1623, h1625, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1627 | h1627
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1628 | h1628
                · linarith only [h0, h1536, h1623, h1627, h1628, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1536, h1618, h1623, h1627, h1628, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1631 | h1631
                · linarith only [h0, h1625, h1627, h1631, h2, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h1618, h1625, h1627, h1631, h2, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1634 | h1634
      · linarith only [h0, h1634, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1636 | h1636
        · linarith only [h0, h1536, h1618, h1636, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1638 | h1638
          · linarith only [h1, h1638, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1640 | h1640
            · linarith only [h0, h1536, h1638, h1640, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1642 | h1642
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1643 | h1643
                · linarith only [h0, h1618, h1638, h1643, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1645 | h1645
                  · linarith only [h1, h1536, h1634, h1642, h1643, h1645, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1647 | h1647
                    · linarith only [h1, h1536, h1636, h1643, h1647, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1649 | h1649
                      · linarith only [h1, h1536, h1640, h1649, hlam]
                      · linarith only [h1, h1536, h1643, h1649, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1652 | h1652
                · linarith only [h0, h1618, h1652, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1654 | h1654
                  · linarith only [h1, h1642, h1652, h1654, h2, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1656 | h1656
                    · linarith only [h1, h1636, h1642, h1652, h1656, h2, hc02, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1658 | h1658
                      · linarith only [h1, h1618, h1640, h1658, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1536, h1658, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
