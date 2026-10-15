import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S0
import Jsp000404.R1LeavesN7_11S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h416 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h417 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h419 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h421 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 3 4 5 (by decide) (by decide) with h1068 | h1068
  · rcases h2bigk with h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      rcases p1069_3 (m.d 0 2) (by simp) with h1071 | h1071
      · rcases p1069_3 (m.d 1 2) (by simp) with h1072 | h1072
        · linarith only [h0, h1072, hlam]
        · rcases p1069_3 (m.d 2 3) (by simp) with h1074 | h1074
          · linarith only [h1074, h3, hlam]
          · rcases p1069_3 (m.d 2 4) (by simp) with h1076 | h1076
            · linarith only [h1076, h4, hlam]
            · rcases p1069_3 (m.d 2 5) (by simp) with h1078 | h1078
              · linarith only [h1078, h5, hlam]
              · rcases h3bigk with h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  rcases p1080_3 (m.d 0 3) (by simp) with h1082 | h1082
                  · rcases p1080_3 (m.d 1 3) (by simp) with h1083 | h1083
                    · linarith only [h1, h1083, hlam]
                    · rcases p1080_3 (m.d 2 3) (by simp) with h1085 | h1085
                      · linarith only [h1085, h3, hlam]
                      · rcases p1080_3 (m.d 3 4) (by simp) with h1087 | h1087
                        · linarith only [h1087, h6, hlam]
                        · linarith only [h1087, h11, hlam]
                  · linarith only [h1, h1082, hlam]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h11, h416, h417, h421, h6, hlam, p1080_2]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h0, h11, h3, h416, h417, h421, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1080_1]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  rcases p1080_3 (m.d 0 3) (by simp) with h1093 | h1093
                  · rcases p1080_3 (m.d 1 3) (by simp) with h1094 | h1094
                    · linarith only [h1, h1094, hlam]
                    · rcases p1080_3 (m.d 2 3) (by simp) with h1096 | h1096
                      · linarith only [h1096, h3, hlam]
                      · rcases p1080_3 (m.d 3 4) (by simp) with h1098 | h1098
                        · linarith only [h1098, h6, hlam]
                        · linarith only [h1068, h1098, hlam]
                  · linarith only [h1093, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h1, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1, p1080_1]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h11, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h355, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h3, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h9, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h417, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h419, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h6, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  rcases p1080_3 (m.d 0 3) (by simp) with h1113 | h1113
                  · rcases p1080_3 (m.d 1 3) (by simp) with h1114 | h1114
                    · linarith only [h1114, hlam, p1080_0]
                    · rcases p1080_3 (m.d 2 3) (by simp) with h1116 | h1116
                      · linarith only [h1116, h417, hlam]
                      · rcases p1080_3 (m.d 3 4) (by simp) with h1118 | h1118
                        · rcases p1080_3 (m.d 3 5) (by simp) with h1119 | h1119
                          · linarith only [h1068, h1119, hlam]
                          · linarith only [h1119, h355, hlam]
                        · linarith only [h1118, hlam, p1080_0]
                  · linarith only [h1, h1113, hlam]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  rcases p1080_3 (m.d 0 3) (by simp) with h1124 | h1124
                  · rcases p1080_3 (m.d 1 3) (by simp) with h1125 | h1125
                    · linarith only [h11, h1125, hlam]
                    · linarith only [h1125, h9, hlam]
                  · linarith only [h1124, h3, hlam]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h0, h3, h355, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1080_1]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h7, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  rcases p1080_3 (m.d 0 3) (by simp) with h1132 | h1132
                  · rcases p1080_3 (m.d 1 3) (by simp) with h1133 | h1133
                    · linarith only [h1133, hlam, p1080_0]
                    · rcases p1080_3 (m.d 2 3) (by simp) with h1135 | h1135
                      · linarith only [h1135, h419, hlam]
                      · rcases p1080_3 (m.d 3 4) (by simp) with h1137 | h1137
                        · rcases p1080_3 (m.d 3 5) (by simp) with h1138 | h1138
                          · rcases h5bigk with h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h3, h416, h417, h421, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              rcases p1139_3 (m.d 0 5) (by simp) with h1142 | h1142
                              · rcases p1139_3 (m.d 1 5) (by simp) with h1143 | h1143
                                · linarith only [h1143, h2, hlam]
                                · linarith only [h10, h1143, hlam]
                              · linarith only [h1142, h5, hlam]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1080_1, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h3, h417, h421, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h2, hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h355, hlam, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h10, h417, h421, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h5, hlam, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h10, hlam, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h419, hlam, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h421, hlam, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h7, hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h0, h1068, h3, h417, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h8, hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h416, hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h416, h417, h421, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1139_1]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [h1068, hlam, p1139_0]
                            · have p1139_0 := h1139c.1
                              have p1139_1 := h1139c.2.1
                              have p1139_2 := h1139c.2.2.1
                              have p1139_3 := h1139c.2.2.2
                              linarith only [hlam, p1139_0]
                          · linarith only [h1138, hlam, p1080_0]
                        · linarith only [h11, h1137, hlam]
                  · linarith only [h1, h1132, hlam]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  rcases p1080_3 (m.d 0 3) (by simp) with h1172 | h1172
                  · rcases p1080_3 (m.d 1 3) (by simp) with h1173 | h1173
                    · linarith only [h1173, h355, hlam]
                    · linarith only [h1173, h9, hlam]
                  · linarith only [h1172, h3, hlam]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [h1068, hlam, p1080_0]
                · have p1080_0 := h1080c.1
                  have p1080_1 := h1080c.2.1
                  have p1080_2 := h1080c.2.2.1
                  have p1080_3 := h1080c.2.2.2
                  linarith only [hlam, p1080_0]
      · linarith only [h0, h1071, hlam]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h11, h3, h416, h417, h421, h6, hlam, p1069_2]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h11, h3, h416, h421, h6, hlam, p1069_2]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      rcases p1069_3 (m.d 0 2) (by simp) with h1182 | h1182
      · rcases p1069_3 (m.d 1 2) (by simp) with h1183 | h1183
        · linarith only [h0, h1183, hlam]
        · linarith only [h10, h1183, hlam]
      · linarith only [h1182, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h0, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      rcases p1069_3 (m.d 0 2) (by simp) with h1189 | h1189
      · rcases p1069_3 (m.d 1 2) (by simp) with h1190 | h1190
        · rcases p1069_3 (m.d 2 3) (by simp) with h1191 | h1191
          · linarith only [h1191, hlam, p1069_0]
          · rcases p1069_3 (m.d 2 4) (by simp) with h1193 | h1193
            · linarith only [h0, h11, h1193, h3, h416, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1]
            · linarith only [h1193, h417, hlam]
        · linarith only [h1190, hlam, p1069_0]
      · linarith only [h1189, h3, hlam]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      rcases p1069_3 (m.d 0 2) (by simp) with h1198 | h1198
      · rcases p1069_3 (m.d 1 2) (by simp) with h1199 | h1199
        · rcases p1069_3 (m.d 2 3) (by simp) with h1200 | h1200
          · linarith only [h1200, h9, hlam]
          · rcases p1069_3 (m.d 2 4) (by simp) with h1202 | h1202
            · linarith only [h1202, hlam, p1069_0]
            · rcases p1069_3 (m.d 2 5) (by simp) with h1204 | h1204
              · linarith only [h10, h1204, hlam]
              · linarith only [h1204, h421, hlam]
        · linarith only [h1199, hlam, p1069_0]
      · linarith only [h1198, h4, hlam]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      rcases p1069_3 (m.d 0 2) (by simp) with h1209 | h1209
      · rcases p1069_3 (m.d 1 2) (by simp) with h1210 | h1210
        · rcases p1069_3 (m.d 2 3) (by simp) with h1211 | h1211
          · linarith only [h1211, h9, hlam]
          · rcases p1069_3 (m.d 2 4) (by simp) with h1213 | h1213
            · linarith only [h1213, h421, hlam, p1069_1]
            · rcases p1069_3 (m.d 2 5) (by simp) with h1215 | h1215
              · linarith only [h1215, hlam, p1069_0]
              · rcases h3bigk with h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  rcases p1217_3 (m.d 0 3) (by simp) with h1219 | h1219
                  · rcases p1217_3 (m.d 1 3) (by simp) with h1220 | h1220
                    · linarith only [h1, h1220, hlam]
                    · rcases p1217_3 (m.d 2 3) (by simp) with h1222 | h1222
                      · linarith only [h1222, h3, hlam]
                      · rcases p1217_3 (m.d 3 4) (by simp) with h1224 | h1224
                        · linarith only [h1224, h6, hlam]
                        · linarith only [h11, h1224, hlam]
                  · linarith only [h1, h1219, hlam]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h11, h416, h417, h421, h6, hlam, p1217_2]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, h11, h3, h416, h417, h421, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  rcases p1217_3 (m.d 0 3) (by simp) with h1230 | h1230
                  · rcases p1217_3 (m.d 1 3) (by simp) with h1231 | h1231
                    · linarith only [h1, h1231, hlam]
                    · rcases p1217_3 (m.d 2 3) (by simp) with h1233 | h1233
                      · linarith only [h1233, h3, hlam]
                      · rcases p1217_3 (m.d 3 4) (by simp) with h1235 | h1235
                        · linarith only [h1235, h6, hlam]
                        · linarith only [h1068, h1235, hlam]
                  · linarith only [h1230, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h355, hc23, hc35, hlam, hphi, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h11, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h355, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h3, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h9, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h417, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h419, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h6, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  rcases p1217_3 (m.d 0 3) (by simp) with h1250 | h1250
                  · rcases p1217_3 (m.d 1 3) (by simp) with h1251 | h1251
                    · linarith only [h1251, hlam, p1217_0]
                    · rcases p1217_3 (m.d 2 3) (by simp) with h1253 | h1253
                      · linarith only [h1253, h417, hlam]
                      · rcases p1217_3 (m.d 3 4) (by simp) with h1255 | h1255
                        · rcases p1217_3 (m.d 3 5) (by simp) with h1256 | h1256
                          · linarith only [h1068, h1256, hlam]
                          · linarith only [h1256, h355, hlam]
                        · linarith only [h1255, hlam, p1217_0]
                  · linarith only [h1, h1250, hlam]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  rcases p1217_3 (m.d 0 3) (by simp) with h1261 | h1261
                  · rcases p1217_3 (m.d 1 3) (by simp) with h1262 | h1262
                    · linarith only [h11, h1262, hlam]
                    · linarith only [h1262, h9, hlam]
                  · linarith only [h1261, h3, hlam]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, h3, h355, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h7, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  rcases p1217_3 (m.d 0 3) (by simp) with h1269 | h1269
                  · rcases p1217_3 (m.d 1 3) (by simp) with h1270 | h1270
                    · linarith only [h1270, hlam, p1217_0]
                    · rcases p1217_3 (m.d 2 3) (by simp) with h1272 | h1272
                      · linarith only [h1272, h419, hlam]
                      · rcases p1217_3 (m.d 3 4) (by simp) with h1274 | h1274
                        · rcases p1217_3 (m.d 3 5) (by simp) with h1275 | h1275
                          · rcases h5bigk with h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h3, h416, h417, h421, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              rcases p1276_3 (m.d 0 5) (by simp) with h1279 | h1279
                              · rcases p1276_3 (m.d 1 5) (by simp) with h1280 | h1280
                                · linarith only [h1280, h2, hlam]
                                · linarith only [h10, h1280, hlam]
                              · linarith only [h1279, h5, hlam]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1217_1, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h3, h417, h421, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h2, hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h2, h417, h421, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h355, hlam, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h11, h3, h416, h417, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h5, hlam, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h10, hlam, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h419, hlam, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h421, hlam, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h7, hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h3, h417, h421, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h0, h1068, h3, h417, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h8, hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h416, hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h417, h421, hc23, hc45, hlam, hphi, ht34, p1276_1]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [h1068, hlam, p1276_0]
                            · have p1276_0 := h1276c.1
                              have p1276_1 := h1276c.2.1
                              have p1276_2 := h1276c.2.2.1
                              have p1276_3 := h1276c.2.2.2
                              linarith only [hlam, p1276_0]
                          · linarith only [h1275, hlam, p1217_0]
                        · linarith only [h11, h1274, hlam]
                  · linarith only [h1, h1269, hlam]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  rcases p1217_3 (m.d 0 3) (by simp) with h1309 | h1309
                  · rcases p1217_3 (m.d 1 3) (by simp) with h1310 | h1310
                    · linarith only [h1310, h355, hlam]
                    · linarith only [h1310, h9, hlam]
                  · linarith only [h1309, h3, hlam]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1068, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
        · linarith only [h1210, hlam, p1069_0]
      · linarith only [h1209, h5, hlam]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h3, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h9, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h417, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h419, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h4, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h0, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h0, h11, h3, h416, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h421, hlam, p1069_1]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h5, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h10, hlam, p1069_0]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [h0, h11, h3, h416, h421, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1069_1]
    · have p1069_0 := h1069c.1
      have p1069_1 := h1069c.2.1
      have p1069_2 := h1069c.2.2.1
      have p1069_3 := h1069c.2.2.2
      linarith only [hlam, p1069_0]
  · linarith only [h1068, h11, h416, hlam]

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h416 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h417 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h419 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416 h417 h419 h421
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416 h417 h419 h421

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h416 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h417 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416 h417 h419
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416 h417 h419

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h416 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 2 3 4 (by decide) (by decide) with h417 | h417
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416 h417
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416 h417

end R2N4
