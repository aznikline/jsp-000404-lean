import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1103 | h1103
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1104 | h1104
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1105 | h1105
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1106 | h1106
          · linarith only [h1106, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1108 | h1108
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1109 | h1109
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1110 | h1110
                · linarith only [h1110, h2, h8, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1112 | h1112
                  · linarith only [h1102, h1108, h1112, h2, h8, hc12, hlam, hphi, u1ehi3]
                  · rcases h3bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      rcases p1114_3 (m.d 0 3) (by simp) with h1116 | h1116
                      · rcases p1114_3 (m.d 1 3) (by simp) with h1117 | h1117
                        · linarith only [h1, h1117, hlam]
                        · rcases p1114_3 (m.d 2 3) (by simp) with h1119 | h1119
                          · linarith only [h1119, h4, hlam]
                          · rcases p1114_3 (m.d 3 4) (by simp) with h1121 | h1121
                            · linarith only [h1121, h6, hlam]
                            · rcases p1114_3 (m.d 3 5) (by simp) with h1123 | h1123
                              · linarith only [h1123, h7, hlam]
                              · rcases h5bigk with h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h8, hc45, hlam, hphi, ht12, ht23, ht34, p1125_1, u1ehi4]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1109, h1112, h8, hc34, hc45, hlam, hphi, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1112, h8, hc34, hc45, hlam, hphi, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h8, hlam, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h3, hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1109, h1112, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h0, h1105, h1112, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1106, hlam, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h5, hlam, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1103, hlam, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h0, h1112, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1110, hlam, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h7, hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1105, hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1109, hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [hlam, p1125_0]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1112, hlam, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, p1125_1, u1ehi4]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p1125_1, u1ehi4]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1109, h1112, hc34, hc45, hlam, hphi, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [h1112, hc34, hc45, hlam, hphi, p1125_1]
                                · have p1125_0 := h1125c.1
                                  have p1125_1 := h1125c.2.1
                                  have p1125_2 := h1125c.2.2.1
                                  have p1125_3 := h1125c.2.2.2
                                  linarith only [hlam, p1125_0]
                      · linarith only [h1, h1116, hlam]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      rcases p1114_3 (m.d 0 3) (by simp) with h1152 | h1152
                      · rcases p1114_3 (m.d 1 3) (by simp) with h1153 | h1153
                        · linarith only [h1, h1153, hlam]
                        · linarith only [h1102, h1153, hlam]
                      · linarith only [h1152, h4, hlam]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      rcases p1114_3 (m.d 0 3) (by simp) with h1157 | h1157
                      · rcases p1114_3 (m.d 1 3) (by simp) with h1158 | h1158
                        · linarith only [h1, h1158, hlam]
                        · linarith only [h1104, h1158, hlam]
                      · linarith only [h1157, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      rcases p1114_3 (m.d 0 3) (by simp) with h1162 | h1162
                      · rcases p1114_3 (m.d 1 3) (by simp) with h1163 | h1163
                        · linarith only [h1, h1163, hlam]
                        · linarith only [h1105, h1163, hlam]
                      · linarith only [h1162, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1, h1108, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      rcases p1114_3 (m.d 0 3) (by simp) with h1170 | h1170
                      · rcases p1114_3 (m.d 1 3) (by simp) with h1171 | h1171
                        · rcases p1114_3 (m.d 2 3) (by simp) with h1172 | h1172
                          · linarith only [h1102, h1172, hlam]
                          · linarith only [h1108, h1172, hlam]
                        · linarith only [h1171, hlam, p1114_0]
                      · linarith only [h1170, h6, hlam]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      rcases p1114_3 (m.d 0 3) (by simp) with h1177 | h1177
                      · rcases p1114_3 (m.d 1 3) (by simp) with h1178 | h1178
                        · rcases p1114_3 (m.d 2 3) (by simp) with h1179 | h1179
                          · linarith only [h1102, h1179, hlam]
                          · linarith only [h1109, h1179, hlam]
                        · linarith only [h1178, hlam, p1114_0]
                      · linarith only [h1177, h7, hlam]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h4, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1102, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h0, h1102, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h0, h1102, h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h6, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1104, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1108, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1112, hlam, p1114_1]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h7, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1105, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h1109, hlam, p1114_0]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [h0, h1103, h1109, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1]
                    · have p1114_0 := h1114c.1
                      have p1114_1 := h1114c.2.1
                      have p1114_2 := h1114c.2.2.1
                      have p1114_3 := h1114c.2.2.2
                      linarith only [hlam, p1114_0]
              · linarith only [h0, h1102, h1105, h1108, h1109, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1200 | h1200
              · linarith only [h1, h1104, h1108, h1200, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                · linarith only [h1202, h2, h8, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1204 | h1204
                  · linarith only [h1104, h1204, h2, h8, hlam]
                  · rcases h3bigk with h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1105, h1108, h1204, h4, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      rcases p1206_3 (m.d 0 3) (by simp) with h1209 | h1209
                      · rcases p1206_3 (m.d 1 3) (by simp) with h1210 | h1210
                        · linarith only [h1, h1210, hlam]
                        · linarith only [h1102, h1210, hlam]
                      · linarith only [h1209, h4, hlam]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      rcases p1206_3 (m.d 0 3) (by simp) with h1214 | h1214
                      · rcases p1206_3 (m.d 1 3) (by simp) with h1215 | h1215
                        · linarith only [h1, h1215, hlam]
                        · linarith only [h1104, h1215, hlam]
                      · linarith only [h1214, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      rcases p1206_3 (m.d 0 3) (by simp) with h1219 | h1219
                      · rcases p1206_3 (m.d 1 3) (by simp) with h1220 | h1220
                        · linarith only [h1, h1220, hlam]
                        · linarith only [h1105, h1220, hlam]
                      · linarith only [h1219, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      rcases p1206_3 (m.d 0 3) (by simp) with h1226 | h1226
                      · rcases p1206_3 (m.d 1 3) (by simp) with h1227 | h1227
                        · rcases p1206_3 (m.d 2 3) (by simp) with h1228 | h1228
                          · linarith only [h1102, h1228, hlam]
                          · rcases p1206_3 (m.d 3 4) (by simp) with h1230 | h1230
                            · linarith only [h1104, h1230, hlam]
                            · linarith only [h1108, h1230, hlam]
                        · linarith only [h1102, h1227, hlam]
                      · linarith only [h1226, h4, hlam]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h0, h1102, h1108, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h0, h1102, h1108, h1204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h4, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1102, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1108, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1200, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h6, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1104, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1204, hlam, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h7, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h1105, hlam, p1206_0]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h0, h1102, h1105, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [h0, h1102, h1105, h1108, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1206_1]
                    · have p1206_0 := h1206c.1
                      have p1206_1 := h1206c.2.1
                      have p1206_2 := h1206c.2.2.1
                      have p1206_3 := h1206c.2.2.2
                      linarith only [hlam, p1206_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1252 | h1252
          · linarith only [h1252, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1254 | h1254
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1255 | h1255
              · linarith only [h1105, h1255, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1257 | h1257
                · linarith only [h1104, h1105, h1257, h7, h8, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1259 | h1259
                  · linarith only [h1104, h1105, h1259, h7, h8, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · rcases h3bigk with h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      rcases p1261_3 (m.d 0 3) (by simp) with h1263 | h1263
                      · rcases p1261_3 (m.d 1 3) (by simp) with h1264 | h1264
                        · linarith only [h1, h1264, hlam]
                        · rcases p1261_3 (m.d 2 3) (by simp) with h1266 | h1266
                          · linarith only [h1266, h4, hlam]
                          · rcases p1261_3 (m.d 3 4) (by simp) with h1268 | h1268
                            · linarith only [h1268, h6, hlam]
                            · rcases p1261_3 (m.d 3 5) (by simp) with h1270 | h1270
                              · linarith only [h1270, h7, hlam]
                              · linarith only [h1105, h1270, hlam]
                      · linarith only [h1, h1263, hlam]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      rcases p1261_3 (m.d 0 3) (by simp) with h1274 | h1274
                      · rcases p1261_3 (m.d 1 3) (by simp) with h1275 | h1275
                        · linarith only [h1, h1275, hlam]
                        · linarith only [h1102, h1275, hlam]
                      · linarith only [h1274, h4, hlam]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1102, h1105, h1254, h7, hlam, p1261_2]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h0, h1104, h1105, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1261_1, u1ehi3]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1105, h1254, h7, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1261_1]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h0, h1105, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1261_1]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1105, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h4, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1102, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h0, h1102, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1261_1]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1255, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h6, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1104, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1254, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h1259, hlam, p1261_1]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h7, hlam, p1261_0]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1261_1, u1ehi2]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [h0, h1254, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1261_1]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      rcases p1261_3 (m.d 0 3) (by simp) with h1299 | h1299
                      · rcases p1261_3 (m.d 1 3) (by simp) with h1300 | h1300
                        · linarith only [h1105, h1300, hlam]
                        · linarith only [h1104, h1300, hlam]
                      · linarith only [h1299, h6, hlam]
                    · have p1261_0 := h1261c.1
                      have p1261_1 := h1261c.2.1
                      have p1261_2 := h1261c.2.2.1
                      have p1261_3 := h1261c.2.2.2
                      linarith only [hlam, p1261_0]
            · linarith only [h0, h1104, h1105, h1254, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h1104, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1307 | h1307
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
        · linarith only [h1102, h1103, h1308, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1310 | h1310
          · linarith only [h1310, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1312 | h1312
            · linarith only [h1102, h1103, h1312, h5, h8, hc34, hc45, hlam, hphi]
            · linarith only [h1307, h1308, h1312, hc23, hc35, hlam, hphi]
      · linarith only [h1307, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1316 | h1316
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1317 | h1317
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1318 | h1318
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1319 | h1319
          · linarith only [h1319, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1322 | h1322
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1323 | h1323
                · linarith only [h1323, h2, h8, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1325 | h1325
                  · linarith only [h1316, h1321, h1323, h1325, h2, h8, hc12, hlam, hphi, u1ehi3]
                  · rcases h3bigk with h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c | h1327c
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1329 | h1329
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1330 | h1330
                        · linarith only [h1, h1330, hlam]
                        · rcases p1327_3 (m.d 2 3) (by simp) with h1332 | h1332
                          · linarith only [h1332, h4, hlam]
                          · linarith only [h1102, h1332, hlam]
                      · linarith only [h1, h1329, hlam]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h0, h1102, h1316, h1323, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1327_1]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1337 | h1337
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1338 | h1338
                        · linarith only [h1, h1338, hlam]
                        · linarith only [h1317, h1338, hlam]
                      · linarith only [h1337, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1342 | h1342
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1343 | h1343
                        · linarith only [h1, h1343, hlam]
                        · linarith only [h1318, h1343, hlam]
                      · linarith only [h1342, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1102, hlam, p1327_1]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1350 | h1350
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1351 | h1351
                        · rcases p1327_3 (m.d 2 3) (by simp) with h1352 | h1352
                          · rcases p1327_3 (m.d 3 4) (by simp) with h1353 | h1353
                            · linarith only [h1353, hlam, p1327_0]
                            · rcases p1327_3 (m.d 3 5) (by simp) with h1355 | h1355
                              · linarith only [h1318, h1355, hlam]
                              · linarith only [h1325, h1355, hlam]
                          · linarith only [h1321, h1352, hlam]
                        · linarith only [h1351, hlam, p1327_0]
                      · linarith only [h1350, h6, hlam]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1361 | h1361
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1362 | h1362
                        · rcases p1327_3 (m.d 2 3) (by simp) with h1363 | h1363
                          · rcases p1327_3 (m.d 3 4) (by simp) with h1364 | h1364
                            · linarith only [h1317, h1364, hlam]
                            · rcases p1327_3 (m.d 3 5) (by simp) with h1366 | h1366
                              · linarith only [h1366, hlam, p1327_0]
                              · rcases h5bigk with h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c | h1368c
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1319, h8, hc45, hlam, hphi, ht12, ht23, ht34, p1368_1, u1ehi3]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1321, h1323, h8, hc34, hc45, hlam, hphi, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1325, h8, hc34, hc45, hlam, hphi, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h8, hlam, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h3, hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1102, h1316, h1321, h1323, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h0, h1102, h1316, h1325, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1319, hlam, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h5, hlam, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1316, hlam, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h0, h1325, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1323, hlam, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h7, hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1318, hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1322, hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [hlam, p1368_0]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1325, hlam, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1319, h3, hc45, hlam, hphi, ht12, ht23, ht34, p1368_1, u1ehi3]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1319, hc45, hlam, hphi, ht12, ht23, ht34, p1368_1, u1ehi3]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1322, h1325, hc34, hc45, hlam, hphi, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [h1325, hc34, hc45, hlam, hphi, p1368_1]
                                · have p1368_0 := h1368c.1
                                  have p1368_1 := h1368c.2.1
                                  have p1368_2 := h1368c.2.2.1
                                  have p1368_3 := h1368c.2.2.2
                                  linarith only [hlam, p1368_0]
                          · linarith only [h1322, h1363, hlam]
                        · linarith only [h1362, hlam, p1327_0]
                      · linarith only [h1361, h7, hlam]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h4, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1327_1, u1ehi2]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1400 | h1400
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1401 | h1401
                        · linarith only [h1102, h1401, hlam]
                        · linarith only [h1317, h1401, hlam]
                      · linarith only [h1400, h6, hlam]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      rcases p1327_3 (m.d 0 3) (by simp) with h1405 | h1405
                      · rcases p1327_3 (m.d 1 3) (by simp) with h1406 | h1406
                        · linarith only [h1102, h1406, hlam]
                        · linarith only [h1318, h1406, hlam]
                      · linarith only [h1405, h7, hlam]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h6, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1317, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1321, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1325, hlam, p1327_1]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h7, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1318, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h1322, hlam, p1327_0]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [h0, h1316, h1322, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1327_1]
                    · have p1327_0 := h1327c.1
                      have p1327_1 := h1327c.2.1
                      have p1327_2 := h1327c.2.2.1
                      have p1327_3 := h1327c.2.2.2
                      linarith only [hlam, p1327_0]
              · linarith only [h1102, h1322, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h1102, h1316, h1319, h1321, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h1102, h1316, h1318, hlam]
      · linarith only [h1102, h1317, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1424 | h1424
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1425 | h1425
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1426 | h1426
          · linarith only [h1426, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1428 | h1428
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1429 | h1429
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1430 | h1430
                · linarith only [h1316, h1430, h5, h8, hc24, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1432 | h1432
                  · linarith only [h1316, h1424, h1432, h5, h8, hc13, hlam, hphi, u1ehi1]
                  · rcases h3bigk with h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1436 | h1436
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1437 | h1437
                        · linarith only [h1, h1437, hlam]
                        · rcases p1434_3 (m.d 2 3) (by simp) with h1439 | h1439
                          · linarith only [h1439, h4, hlam]
                          · linarith only [h1102, h1439, hlam]
                      · linarith only [h1, h1436, hlam]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h0, h1102, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1434_1, u1ehi1]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1444 | h1444
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1445 | h1445
                        · linarith only [h1, h1445, hlam]
                        · linarith only [h1424, h1445, hlam]
                      · linarith only [h1444, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1449 | h1449
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1450 | h1450
                        · linarith only [h1, h1450, hlam]
                        · linarith only [h1425, h1450, hlam]
                      · linarith only [h1449, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1102, hlam, p1434_1]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1457 | h1457
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1458 | h1458
                        · rcases p1434_3 (m.d 2 3) (by simp) with h1459 | h1459
                          · rcases p1434_3 (m.d 3 4) (by simp) with h1460 | h1460
                            · linarith only [h1460, hlam, p1434_0]
                            · rcases p1434_3 (m.d 3 5) (by simp) with h1462 | h1462
                              · linarith only [h1425, h1462, hlam]
                              · linarith only [h1432, h1462, hlam]
                          · linarith only [h1428, h1459, hlam]
                        · linarith only [h1458, hlam, p1434_0]
                      · linarith only [h1457, h6, hlam]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1468 | h1468
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1469 | h1469
                        · rcases p1434_3 (m.d 2 3) (by simp) with h1470 | h1470
                          · rcases p1434_3 (m.d 3 4) (by simp) with h1471 | h1471
                            · linarith only [h1424, h1471, hlam]
                            · rcases p1434_3 (m.d 3 5) (by simp) with h1473 | h1473
                              · linarith only [h1473, hlam, p1434_0]
                              · rcases h5bigk with h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1426, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1475_1, u1ehi3]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1316, h8, hc45, hlam, hphi, ht12, ht23, ht34, p1475_1, u1ehi1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1432, h8, hc34, hc45, hlam, hphi, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h8, hlam, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h3, hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1316, hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1432, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1426, hlam, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h5, hlam, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht12, p1475_1, u1ehi4]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h0, h1429, h1432, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1430, hlam, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h7, hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1425, hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1429, hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [hlam, p1475_0]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1432, hlam, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1316, h3, hc45, hlam, hphi, ht12, ht23, ht34, p1475_1, u1ehi1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1316, hc45, hlam, hphi, ht12, ht23, ht34, p1475_1, u1ehi1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1316, hc45, hlam, hphi, ht12, ht23, ht34, p1475_1, u1ehi1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [h1432, hc34, hc45, hlam, hphi, p1475_1]
                                · have p1475_0 := h1475c.1
                                  have p1475_1 := h1475c.2.1
                                  have p1475_2 := h1475c.2.2.1
                                  have p1475_3 := h1475c.2.2.2
                                  linarith only [hlam, p1475_0]
                          · linarith only [h1429, h1470, hlam]
                        · linarith only [h1469, hlam, p1434_0]
                      · linarith only [h1468, h7, hlam]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h4, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1434_1, u1ehi2]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1507 | h1507
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1508 | h1508
                        · linarith only [h1102, h1508, hlam]
                        · linarith only [h1424, h1508, hlam]
                      · linarith only [h1507, h6, hlam]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      rcases p1434_3 (m.d 0 3) (by simp) with h1512 | h1512
                      · rcases p1434_3 (m.d 1 3) (by simp) with h1513 | h1513
                        · linarith only [h1102, h1513, hlam]
                        · linarith only [h1425, h1513, hlam]
                      · linarith only [h1512, h7, hlam]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h6, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1424, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1428, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1432, hlam, p1434_1]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h7, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1425, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1429, hlam, p1434_0]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [h1, h1425, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1434_1]
                    · have p1434_0 := h1434c.1
                      have p1434_1 := h1434c.2.1
                      have p1434_2 := h1434c.2.2.1
                      have p1434_3 := h1434c.2.2.2
                      linarith only [hlam, p1434_0]
              · linarith only [h0, h1102, h1429, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h1102, h1428, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1529 | h1529
          · linarith only [h1529, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1531 | h1531
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1532 | h1532
              · linarith only [h0, h1424, h1425, h1532, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1102, h1532, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h1102, h1531, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h1102, h1424, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h1537 | h1537
  · linarith only [h1537, h6, h7, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1539 | h1539
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1540 | h1540
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1541 | h1541
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1542 | h1542
          · linarith only [h1, h1542, h7, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1544 | h1544
            · linarith only [h1537, h1544, h2, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1546 | h1546
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1547 | h1547
                · linarith only [h1, h1539, h1547, h7, hc12, hlam, hphi, u1ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1549 | h1549
                  · linarith only [h1537, h1549, h2, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1551 | h1551
                    · linarith only [h1, h1537, h1539, h1546, h1551, h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h3bigk with h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1551, h7, hc13, hc45, hlam, hphi, ht34, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1551, h7, hc23, hc45, hlam, hphi, ht34, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1551, h7, hc34, hc45, hlam, hphi, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h7, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1, h1546, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1, h1551, h7, hc34, hc45, hlam, hphi, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1542, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h4, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1539, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1551, h4, h7, hc34, hc45, hlam, hphi, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1547, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h6, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1541, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1546, hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [hlam, p1553_0]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1551, hlam, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1, h1551, hc45, hlam, hphi, ht12, ht23, ht34, p1553_1, u1ehi2]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1541, h1551, hc45, hlam, hphi, ht12, ht23, ht34, p1553_1, u1ehi3]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [h1546, h1551, hc34, hc45, hlam, hphi, p1553_1]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        rcases p1553_3 (m.d 0 3) (by simp) with h1577 | h1577
                        · linarith only [h1577, h7, hlam]
                        · linarith only [h1577, h6, hlam]
                      · have p1553_0 := h1553c.1
                        have p1553_1 := h1553c.2.1
                        have p1553_2 := h1553c.2.2.1
                        have p1553_3 := h1553c.2.2.2
                        linarith only [hlam, p1553_0]
              · linarith only [h1546, h6, h7, hc23, hc35, hlam, hphi]
        · linarith only [h1541, h6, h7, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1583 | h1583
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1584 | h1584
          · linarith only [h1, h1584, h7, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1586 | h1586
            · linarith only [h1537, h1586, h2, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1588 | h1588
              · linarith only [h0, h1539, h1540, h1588, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1588, h6, h7, hc23, hc35, hlam, hphi]
        · linarith only [h1583, h6, h7, hc13, hc35, hlam, hphi]
    · linarith only [h1539, h4, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1593 | h1593
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1594 | h1594
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1595 | h1595
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1596 | h1596
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1597 | h1597
          · linarith only [h0, h1593, h1595, h1597, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1599 | h1599
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1601 | h1601
                · linarith only [h1593, h1595, h1601, h3, h6, hc12, hlam, hphi, u1ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1603 | h1603
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1604 | h1604
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1605 | h1605
                      · rcases h3bigk with h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1599, h6, hc34, hlam, hphi, ht12, ht23, p1606_1, u1ehi4]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h6, hc23, hc34, hlam, hphi, p1606_1]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h6, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          rcases p1606_3 (m.d 0 3) (by simp) with h1611 | h1611
                          · rcases p1606_3 (m.d 1 3) (by simp) with h1612 | h1612
                            · linarith only [h1, h1612, hlam]
                            · linarith only [h1599, h1612, hlam]
                          · linarith only [h1611, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1, h1603, h1605, hc01, hc45, hlam, hphi, ht0b, ht5b, p1606_1]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1597, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          rcases p1606_3 (m.d 0 3) (by simp) with h1620 | h1620
                          · rcases p1606_3 (m.d 1 3) (by simp) with h1621 | h1621
                            · rcases p1606_3 (m.d 2 3) (by simp) with h1622 | h1622
                              · linarith only [h1595, h1622, hlam]
                              · linarith only [h1603, h1622, hlam]
                            · linarith only [h1621, hlam, p1606_0]
                          · linarith only [h1593, h1620, hlam]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h4, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1595, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1601, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h0, h1595, h1605, hc01, hc45, hlam, hphi, ht0b, ht5b, p1606_1]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht12, ht23, p1606_1, u1ehi2]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p1606_1, u1ehi2]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          rcases p1606_3 (m.d 0 3) (by simp) with h1634 | h1634
                          · linarith only [h1634, h6, hlam]
                          · linarith only [h1634, h4, hlam]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          rcases p1606_3 (m.d 0 3) (by simp) with h1638 | h1638
                          · linarith only [h1638, h6, hlam]
                          · linarith only [h1593, h1638, hlam]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1593, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1599, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1603, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [h1605, hlam, p1606_0]
                        · have p1606_0 := h1606c.1
                          have p1606_1 := h1606c.2.1
                          have p1606_2 := h1606c.2.2.1
                          have p1606_3 := h1606c.2.2.2
                          linarith only [hlam, p1606_0]
                      · linarith only [h1593, h1605, h3, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                    · linarith only [h1600, h1601, h1603, h1604, h2, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1593, h1603, h6, hc23, hc34, hlam, hphi]
              · linarith only [h1594, h1600, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h1593, h1599, h6, hc13, hc34, hlam, hphi]
        · linarith only [h1593, h1596, h5, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h1595, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h1593, h1594, h6, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1654 | h1654
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1655 | h1655
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1656 | h1656
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1657 | h1657
          · linarith only [h1, h1657, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1659 | h1659
            · linarith only [h1, h1593, h1659, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1661 | h1661
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1662 | h1662
                · linarith only [h1, h1655, h1662, h6, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1664 | h1664
                  · linarith only [h1, h1593, h1655, h1664, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1667 | h1667
                      · rcases h3bigk with h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1593, h1667, hc34, hlam, hphi, ht12, ht23, p1668_1, u1ehi2]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1593, h1667, hc23, hc34, hlam, hphi, p1668_1]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h6, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1593, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1, h1593, h1667, hc23, hc34, hlam, hphi, p1668_1]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1657, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1659, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h4, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1655, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1662, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1664, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht12, ht23, p1668_1, u1ehi2]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p1668_1, u1ehi2]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          rcases p1668_3 (m.d 0 3) (by simp) with h1686 | h1686
                          · linarith only [h1686, h6, hlam]
                          · linarith only [h1686, h4, hlam]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1, h1593, hc34, hlam, hphi, ht12, ht23, p1668_1, u1ehi2]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p1668_1, u1ehi2]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p1668_1, u1ehi2]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          rcases p1668_3 (m.d 0 3) (by simp) with h1693 | h1693
                          · linarith only [h1593, h1693, hlam]
                          · linarith only [h1693, h4, hlam]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [h1667, hlam, p1668_0]
                        · have p1668_0 := h1668c.1
                          have p1668_1 := h1668c.2.1
                          have p1668_2 := h1668c.2.2.1
                          have p1668_3 := h1668c.2.2.2
                          linarith only [hlam, p1668_0]
                      · linarith only [h1, h1661, h1667, h2, h6, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1699 | h1699
                      · rcases h3bigk with h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h6, hc34, hlam, hphi, ht12, ht23, p1700_1, u1ehi2]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h6, hc23, hc34, hlam, hphi, p1700_1]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h6, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1593, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1, h1593, h1699, hc23, hc34, hlam, hphi, p1700_1]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1657, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1659, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h4, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1655, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1662, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1664, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht12, ht23, p1700_1, u1ehi2]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p1700_1, u1ehi2]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          rcases p1700_3 (m.d 0 3) (by simp) with h1718 | h1718
                          · linarith only [h1718, h6, hlam]
                          · linarith only [h1718, h4, hlam]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1, h1593, hc34, hlam, hphi, ht12, ht23, p1700_1, u1ehi2]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p1700_1, u1ehi2]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p1700_1, u1ehi2]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          rcases p1700_3 (m.d 0 3) (by simp) with h1725 | h1725
                          · linarith only [h1593, h1725, hlam]
                          · linarith only [h1725, h4, hlam]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [h1699, hlam, p1700_0]
                        · have p1700_0 := h1700c.1
                          have p1700_1 := h1700c.2.1
                          have p1700_2 := h1700c.2.2.1
                          have p1700_3 := h1700c.2.2.2
                          linarith only [hlam, p1700_0]
                      · linarith only [h1, h1699, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h1654, h1661, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1732 | h1732
          · linarith only [h1, h1732, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1734 | h1734
            · linarith only [h1, h1593, h1734, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1736 | h1736
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1737 | h1737
                · linarith only [h1654, h1656, h1737, h5, h6, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1739 | h1739
                  · linarith only [h1593, h1655, h1656, h1739, h5, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1741 | h1741
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1742 | h1742
                      · rcases h3bigk with h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h6, hc34, hlam, hphi, ht12, ht23, p1743_1, u1ehi2]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h6, hc23, hc34, hlam, hphi, p1743_1]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h6, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1593, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h0, h1655, h1656, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1743_1]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1732, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1734, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h4, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1655, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1737, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1739, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht12, ht23, p1743_1, u1ehi2]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p1743_1, u1ehi2]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          rcases p1743_3 (m.d 0 3) (by simp) with h1761 | h1761
                          · linarith only [h1761, h6, hlam]
                          · linarith only [h1761, h4, hlam]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1593, h1656, h5, hc12, hc34, hlam, hphi, ht23, p1743_1]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p1743_1, u1ehi2]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p1743_1, u1ehi2]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          rcases p1743_3 (m.d 0 3) (by simp) with h1768 | h1768
                          · linarith only [h1593, h1768, hlam]
                          · linarith only [h1768, h4, hlam]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [h1742, hlam, p1743_0]
                        · have p1743_0 := h1743c.1
                          have p1743_1 := h1743c.2.1
                          have p1743_2 := h1743c.2.2.1
                          have p1743_3 := h1743c.2.2.2
                          linarith only [hlam, p1743_0]
                      · linarith only [h1, h1736, h1742, h6, hc15, hlam, hphi, u1ehi2]
                    · linarith only [h1655, h1656, h1736, h1741, hc14, hlam, hphi, u1ehi2]
              · linarith only [h1654, h1736, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h1655, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1777 | h1777
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1778 | h1778
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1779 | h1779
          · linarith only [h1, h1779, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1781 | h1781
            · linarith only [h1, h1593, h1781, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1783 | h1783
              · linarith only [h1654, h1783, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1785 | h1785
                · linarith only [h1, h1785, h6, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1787 | h1787
                  · linarith only [h1, h1593, h1777, h1787, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1789 | h1789
                    · linarith only [h1, h1654, h1789, h6, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1791 | h1791
                      · linarith only [h1, h1654, h1791, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1, h1791, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1794 | h1794
          · linarith only [h1, h1794, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1796 | h1796
            · linarith only [h1593, h1777, h1778, h1796, h3, hc25, hlam, hphi, ht12, u1ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1798 | h1798
              · linarith only [h1, h1654, h1798, h6, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1800 | h1800
                · linarith only [h1, h1777, h1778, h1800, h5, h6, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1802 | h1802
                  · linarith only [h0, h1777, h1778, h1802, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1804 | h1804
                    · linarith only [h1654, h1777, h1778, h1800, h1804, h5, hc23, hc34, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1806 | h1806
                      · linarith only [h1654, h1777, h1778, h1806, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1, h1806, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · linarith only [h1777, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6

end R2N4
