import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S1
import Jsp000404.R1LeavesN7_9S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h969 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h1107 | h1107
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1108 | h1108
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1109 | h1109
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1111 | h1111
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
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
                  linarith only [h0, h1107, h1113, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h0, h1107, h1113, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  rcases p1114_3 (m.d 0 3) (by simp) with h1118 | h1118
                  · rcases p1114_3 (m.d 1 3) (by simp) with h1119 | h1119
                    · linarith only [h1, h1119, hlam]
                    · linarith only [h1107, h1119, hlam]
                  · linarith only [h1118, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  rcases p1114_3 (m.d 0 3) (by simp) with h1123 | h1123
                  · rcases p1114_3 (m.d 1 3) (by simp) with h1124 | h1124
                    · linarith only [h1, h1124, hlam]
                    · linarith only [h1108, h1124, hlam]
                  · linarith only [h1123, hlam, p1114_0]
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
                  linarith only [h9, hlam, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1, h1113, hc01, hc45, hlam, hphi, ht0b, ht5b, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  rcases p1114_3 (m.d 0 3) (by simp) with h1132 | h1132
                  · rcases p1114_3 (m.d 1 3) (by simp) with h1133 | h1133
                    · rcases p1114_3 (m.d 2 3) (by simp) with h1134 | h1134
                      · rcases p1114_3 (m.d 3 4) (by simp) with h1135 | h1135
                        · linarith only [h1107, h1135, hlam]
                        · linarith only [h1113, h1135, hlam]
                      · linarith only [h1111, h1134, hlam]
                    · linarith only [h1133, hlam, p1114_0]
                  · linarith only [h1132, h7, hlam]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h4, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h0, h1107, h1113, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h0, h1113, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  rcases p1114_3 (m.d 0 3) (by simp) with h1145 | h1145
                  · rcases p1114_3 (m.d 1 3) (by simp) with h1146 | h1146
                    · linarith only [h1146, h9, hlam]
                    · linarith only [h1108, h1146, hlam]
                  · linarith only [h1145, h7, hlam]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h6, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1107, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1110, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1, h1107, h1113, hc01, hc45, hlam, hphi, ht0b, ht5b, p1114_1]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h7, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1108, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1111, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [h1113, hlam, p1114_0]
                · have p1114_0 := h1114c.1
                  have p1114_1 := h1114c.2.1
                  have p1114_2 := h1114c.2.2.1
                  have p1114_3 := h1114c.2.2.2
                  linarith only [hlam, p1114_0]
              · rcases h3bigk with h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h0, h1107, h1109, h1113, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1160_1]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h0, h1107, h1109, h1113, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1160_1]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  rcases p1160_3 (m.d 0 3) (by simp) with h1164 | h1164
                  · rcases p1160_3 (m.d 1 3) (by simp) with h1165 | h1165
                    · linarith only [h1, h1165, hlam]
                    · linarith only [h1107, h1165, hlam]
                  · linarith only [h1164, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  rcases p1160_3 (m.d 0 3) (by simp) with h1169 | h1169
                  · rcases p1160_3 (m.d 1 3) (by simp) with h1170 | h1170
                    · linarith only [h1, h1170, hlam]
                    · linarith only [h1108, h1170, hlam]
                  · linarith only [h1169, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h9, hlam, p1160_1]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  rcases p1160_3 (m.d 0 3) (by simp) with h1177 | h1177
                  · rcases p1160_3 (m.d 1 3) (by simp) with h1178 | h1178
                    · rcases p1160_3 (m.d 2 3) (by simp) with h1179 | h1179
                      · rcases p1160_3 (m.d 3 4) (by simp) with h1180 | h1180
                        · linarith only [h1180, hlam, p1160_0]
                        · rcases p1160_3 (m.d 3 5) (by simp) with h1182 | h1182
                          · linarith only [h1108, h1182, hlam]
                          · linarith only [h1113, h1182, hlam]
                      · linarith only [h1110, h1179, hlam]
                    · linarith only [h1178, hlam, p1160_0]
                  · linarith only [h1177, h6, hlam]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  rcases p1160_3 (m.d 0 3) (by simp) with h1188 | h1188
                  · rcases p1160_3 (m.d 1 3) (by simp) with h1189 | h1189
                    · rcases p1160_3 (m.d 2 3) (by simp) with h1190 | h1190
                      · rcases p1160_3 (m.d 3 4) (by simp) with h1191 | h1191
                        · linarith only [h1107, h1191, hlam]
                        · rcases p1160_3 (m.d 3 5) (by simp) with h1193 | h1193
                          · linarith only [h1193, hlam, p1160_0]
                          · rcases h4bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1109, h1113, h6, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              rcases p1195_3 (m.d 0 4) (by simp) with h1199 | h1199
                              · rcases p1195_3 (m.d 1 4) (by simp) with h1200 | h1200
                                · linarith only [h1200, h2, hlam]
                                · linarith only [h1107, h1200, hlam]
                              · linarith only [h1199, h6, hlam]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, h1113, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h2, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h969, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1, h1107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, h1107, h1113, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h5, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, h1110, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, h1110, h1113, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h6, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1107, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1110, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1113, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h8, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1109, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1112, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1109, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                      · linarith only [h1111, h1190, hlam]
                    · linarith only [h1189, hlam, p1160_0]
                  · linarith only [h1188, h7, hlam]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h4, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h0, h1107, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1160_1]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  rcases p1160_3 (m.d 0 3) (by simp) with h1231 | h1231
                  · rcases p1160_3 (m.d 1 3) (by simp) with h1232 | h1232
                    · linarith only [h1232, h9, hlam]
                    · linarith only [h1107, h1232, hlam]
                  · linarith only [h1231, h6, hlam]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  rcases p1160_3 (m.d 0 3) (by simp) with h1236 | h1236
                  · rcases p1160_3 (m.d 1 3) (by simp) with h1237 | h1237
                    · linarith only [h1237, h9, hlam]
                    · linarith only [h1108, h1237, hlam]
                  · linarith only [h1236, h7, hlam]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h6, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1107, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1110, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1113, hlam, p1160_1]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h7, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1108, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1111, hlam, p1160_0]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [h1, h1108, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1160_1]
                · have p1160_0 := h1160c.1
                  have p1160_1 := h1160c.2.1
                  have p1160_2 := h1160c.2.2.1
                  have p1160_3 := h1160c.2.2.2
                  linarith only [hlam, p1160_0]
            · linarith only [h1109, h1112, h969, hlam]
          · linarith only [h1108, h1111, h9, hlam]
        · linarith only [h1107, h1110, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1254 | h1254
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1255 | h1255
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1256 | h1256
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
              · linarith only [h1107, h1109, h1257, hlam]
              · rcases h3bigk with h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c | h1259c
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1261 | h1261
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1262 | h1262
                    · linarith only [h1, h1262, hlam]
                    · rcases p1259_3 (m.d 2 3) (by simp) with h1264 | h1264
                      · linarith only [h1264, h4, hlam]
                      · linarith only [h1264, h9, hlam]
                  · linarith only [h1, h1261, hlam]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h0, h1109, h1254, h1256, h4, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1259_1]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1269 | h1269
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1270 | h1270
                    · linarith only [h1, h1270, hlam]
                    · linarith only [h1107, h1270, hlam]
                  · linarith only [h1269, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1274 | h1274
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1275 | h1275
                    · linarith only [h1, h1275, hlam]
                    · linarith only [h1108, h1275, hlam]
                  · linarith only [h1274, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h9, hlam, p1259_1]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1282 | h1282
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1283 | h1283
                    · rcases p1259_3 (m.d 2 3) (by simp) with h1284 | h1284
                      · rcases p1259_3 (m.d 3 4) (by simp) with h1285 | h1285
                        · linarith only [h1285, hlam, p1259_0]
                        · rcases p1259_3 (m.d 3 5) (by simp) with h1287 | h1287
                          · linarith only [h1108, h1287, hlam]
                          · linarith only [h1257, h1287, hlam]
                      · linarith only [h1254, h1284, hlam]
                    · linarith only [h1283, hlam, p1259_0]
                  · linarith only [h1282, h6, hlam]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1293 | h1293
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1294 | h1294
                    · rcases p1259_3 (m.d 2 3) (by simp) with h1295 | h1295
                      · rcases p1259_3 (m.d 3 4) (by simp) with h1296 | h1296
                        · linarith only [h1107, h1296, hlam]
                        · rcases p1259_3 (m.d 3 5) (by simp) with h1298 | h1298
                          · linarith only [h1298, hlam, p1259_0]
                          · rcases h4bigk with h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              rcases p1300_3 (m.d 0 4) (by simp) with h1302 | h1302
                              · rcases p1300_3 (m.d 1 4) (by simp) with h1303 | h1303
                                · linarith only [h1303, h2, hlam]
                                · rcases p1300_3 (m.d 2 4) (by simp) with h1305 | h1305
                                  · linarith only [h1305, h5, hlam]
                                  · linarith only [h1305, h969, hlam]
                              · linarith only [h1302, h2, hlam]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1109, h1256, h6, h969, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              rcases p1300_3 (m.d 0 4) (by simp) with h1310 | h1310
                              · rcases p1300_3 (m.d 1 4) (by simp) with h1311 | h1311
                                · linarith only [h1311, h2, hlam]
                                · linarith only [h1107, h1311, hlam]
                              · linarith only [h1310, h6, hlam]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h0, h1109, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h2, hlam, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h969, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1109, h8, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1109, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h5, hlam, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h0, h1254, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h0, h1254, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h0, h1254, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h6, hlam, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1107, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1254, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1257, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h8, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h969, hc12, hc45, hlam, hphi, ht23, ht34, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h1256, hlam, p1300_0]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [h0, h1254, h1256, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1300_1]
                            · have p1300_0 := h1300c.1
                              have p1300_1 := h1300c.2.1
                              have p1300_2 := h1300c.2.2.1
                              have p1300_3 := h1300c.2.2.2
                              linarith only [hlam, p1300_0]
                      · linarith only [h1255, h1295, hlam]
                    · linarith only [h1294, hlam, p1259_0]
                  · linarith only [h1293, h7, hlam]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h4, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h0, h1107, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1259_1]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1342 | h1342
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1343 | h1343
                    · linarith only [h1343, h9, hlam]
                    · linarith only [h1107, h1343, hlam]
                  · linarith only [h1342, h6, hlam]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  rcases p1259_3 (m.d 0 3) (by simp) with h1347 | h1347
                  · rcases p1259_3 (m.d 1 3) (by simp) with h1348 | h1348
                    · linarith only [h1348, h9, hlam]
                    · linarith only [h1108, h1348, hlam]
                  · linarith only [h1347, h7, hlam]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h6, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1107, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1254, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1257, hlam, p1259_1]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h7, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1108, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1255, hlam, p1259_0]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [h1, h1108, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1259_1]
                · have p1259_0 := h1259c.1
                  have p1259_1 := h1259c.2.1
                  have p1259_2 := h1259c.2.2.1
                  have p1259_3 := h1259c.2.2.2
                  linarith only [hlam, p1259_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
              · linarith only [h0, h1256, h1362, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases h3bigk with h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1366 | h1366
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1367 | h1367
                    · linarith only [h1, h1367, hlam]
                    · rcases p1364_3 (m.d 2 3) (by simp) with h1369 | h1369
                      · linarith only [h1369, h4, hlam]
                      · linarith only [h1369, h9, hlam]
                  · linarith only [h1, h1366, hlam]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1373 | h1373
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1374 | h1374
                    · linarith only [h1, h1374, hlam]
                    · rcases p1364_3 (m.d 2 3) (by simp) with h1376 | h1376
                      · linarith only [h1376, h4, hlam]
                      · rcases p1364_3 (m.d 3 4) (by simp) with h1378 | h1378
                        · linarith only [h1378, h6, hlam]
                        · rcases p1364_3 (m.d 3 5) (by simp) with h1380 | h1380
                          · linarith only [h1380, h7, hlam]
                          · rcases h4bigk with h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              rcases p1382_3 (m.d 0 4) (by simp) with h1384 | h1384
                              · rcases p1382_3 (m.d 1 4) (by simp) with h1385 | h1385
                                · linarith only [h1385, h2, hlam]
                                · rcases p1382_3 (m.d 2 4) (by simp) with h1387 | h1387
                                  · linarith only [h1387, h5, hlam]
                                  · linarith only [h1387, h969, hlam]
                              · linarith only [h1384, h2, hlam]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h0, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              rcases p1382_3 (m.d 0 4) (by simp) with h1392 | h1392
                              · rcases p1382_3 (m.d 1 4) (by simp) with h1393 | h1393
                                · linarith only [h1393, h2, hlam]
                                · linarith only [h1107, h1393, hlam]
                              · linarith only [h1392, h6, hlam]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h0, h1256, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h2, hlam, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h969, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h1109, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h5, hlam, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h1256, hc14, hc45, hlam, hphi, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h0, h1256, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h1256, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h6, hlam, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h1107, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h1254, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h1362, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h8, hlam, p1382_0]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h0, h4, h6, h8, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h0, h4, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [h0, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1382_1]
                            · have p1382_0 := h1382c.1
                              have p1382_1 := h1382c.2.1
                              have p1382_2 := h1382c.2.2.1
                              have p1382_3 := h1382c.2.2.2
                              linarith only [hlam, p1382_0]
                  · linarith only [h1373, h4, hlam]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1419 | h1419
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1420 | h1420
                    · linarith only [h1, h1420, hlam]
                    · linarith only [h1107, h1420, hlam]
                  · linarith only [h1419, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1424 | h1424
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1425 | h1425
                    · linarith only [h1, h1425, hlam]
                    · linarith only [h1108, h1425, hlam]
                  · linarith only [h1424, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h9, hlam, p1364_1]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1432 | h1432
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1433 | h1433
                    · rcases p1364_3 (m.d 2 3) (by simp) with h1434 | h1434
                      · rcases p1364_3 (m.d 3 4) (by simp) with h1435 | h1435
                        · linarith only [h1435, hlam, p1364_0]
                        · rcases p1364_3 (m.d 3 5) (by simp) with h1437 | h1437
                          · linarith only [h1108, h1437, hlam]
                          · linarith only [h1362, h1437, hlam]
                      · linarith only [h1254, h1434, hlam]
                    · linarith only [h1433, hlam, p1364_0]
                  · linarith only [h1432, h6, hlam]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1443 | h1443
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1444 | h1444
                    · rcases p1364_3 (m.d 2 3) (by simp) with h1445 | h1445
                      · rcases p1364_3 (m.d 3 4) (by simp) with h1446 | h1446
                        · linarith only [h1107, h1446, hlam]
                        · rcases p1364_3 (m.d 3 5) (by simp) with h1448 | h1448
                          · linarith only [h1448, hlam, p1364_0]
                          · rcases h4bigk with h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              rcases p1450_3 (m.d 0 4) (by simp) with h1452 | h1452
                              · rcases p1450_3 (m.d 1 4) (by simp) with h1453 | h1453
                                · linarith only [h1453, h2, hlam]
                                · rcases p1450_3 (m.d 2 4) (by simp) with h1455 | h1455
                                  · linarith only [h1455, h5, hlam]
                                  · linarith only [h1455, h969, hlam]
                              · linarith only [h1452, h2, hlam]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              rcases p1450_3 (m.d 0 4) (by simp) with h1460 | h1460
                              · rcases p1450_3 (m.d 1 4) (by simp) with h1461 | h1461
                                · linarith only [h1461, h2, hlam]
                                · linarith only [h1107, h1461, hlam]
                              · linarith only [h1460, h6, hlam]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h1109, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h2, hlam, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h969, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h1109, hc34, hc45, hlam, hphi, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h1109, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h5, hlam, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h1254, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h1256, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h6, hlam, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h1107, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h1254, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h1362, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h8, hlam, p1450_0]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h4, h6, h8, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h4, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [h0, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1450_1]
                            · have p1450_0 := h1450c.1
                              have p1450_1 := h1450c.2.1
                              have p1450_2 := h1450c.2.2.1
                              have p1450_3 := h1450c.2.2.2
                              linarith only [hlam, p1450_0]
                      · linarith only [h1255, h1445, hlam]
                    · linarith only [h1444, hlam, p1364_0]
                  · linarith only [h1443, h7, hlam]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h4, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h0, h1107, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1364_1]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1492 | h1492
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1493 | h1493
                    · linarith only [h1493, h9, hlam]
                    · linarith only [h1107, h1493, hlam]
                  · linarith only [h1492, h6, hlam]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  rcases p1364_3 (m.d 0 3) (by simp) with h1497 | h1497
                  · rcases p1364_3 (m.d 1 3) (by simp) with h1498 | h1498
                    · linarith only [h1498, h9, hlam]
                    · linarith only [h1108, h1498, hlam]
                  · linarith only [h1497, h7, hlam]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h6, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1107, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1254, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1362, hlam, p1364_1]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h7, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1108, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1255, hlam, p1364_0]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [h1, h1108, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1364_1]
                · have p1364_0 := h1364c.1
                  have p1364_1 := h1364c.2.1
                  have p1364_2 := h1364c.2.2.1
                  have p1364_3 := h1364c.2.2.2
                  linarith only [hlam, p1364_0]
          · linarith only [h1108, h1255, h9, hlam]
        · linarith only [h1107, h1254, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1514 | h1514
      · linarith only [h1107, h1108, h1514, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1516 | h1516
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1517 | h1517
          · linarith only [h0, h1107, h1108, h1517, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
            · linarith only [h0, h1514, h1516, h1517, h1519, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1521 | h1521
              · linarith only [h1, h1107, h1519, h1521, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h3bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  rcases p1523_3 (m.d 0 3) (by simp) with h1525 | h1525
                  · rcases p1523_3 (m.d 1 3) (by simp) with h1526 | h1526
                    · linarith only [h1, h1526, hlam]
                    · rcases p1523_3 (m.d 2 3) (by simp) with h1528 | h1528
                      · linarith only [h1528, h4, hlam]
                      · linarith only [h1528, h9, hlam]
                  · linarith only [h1, h1525, hlam]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  rcases p1523_3 (m.d 0 3) (by simp) with h1532 | h1532
                  · rcases p1523_3 (m.d 1 3) (by simp) with h1533 | h1533
                    · linarith only [h1, h1533, hlam]
                    · rcases p1523_3 (m.d 2 3) (by simp) with h1535 | h1535
                      · linarith only [h1535, h4, hlam]
                      · rcases p1523_3 (m.d 3 4) (by simp) with h1537 | h1537
                        · linarith only [h1537, h6, hlam]
                        · rcases p1523_3 (m.d 3 5) (by simp) with h1539 | h1539
                          · linarith only [h1539, h7, hlam]
                          · linarith only [h1517, h1539, hlam]
                  · linarith only [h1532, h4, hlam]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1107, h1517, h1521, h6, h8, h9, hlam, p1523_2]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h0, h1517, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h9, hlam, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h0, h1517, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1108, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h4, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1517, hc13, hc35, hlam, hphi, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h0, h1517, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1517, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h6, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1107, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1516, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h1521, hlam, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h7, hlam, p1523_0]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h0, h1107, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [h0, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1523_1]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  rcases p1523_3 (m.d 0 3) (by simp) with h1563 | h1563
                  · rcases p1523_3 (m.d 1 3) (by simp) with h1564 | h1564
                    · linarith only [h1108, h1564, hlam]
                    · linarith only [h1107, h1564, hlam]
                  · linarith only [h1563, h6, hlam]
                · have p1523_0 := h1523c.1
                  have p1523_1 := h1523c.2.1
                  have p1523_2 := h1523c.2.2.1
                  have p1523_3 := h1523c.2.2.2
                  linarith only [hlam, p1523_0]
        · linarith only [h1, h1107, h1516, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1570 | h1570
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1571 | h1571
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1572 | h1572
        · linarith only [h0, h1107, h1570, h1572, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1574 | h1574
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1575 | h1575
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1576 | h1576
              · rcases h3bigk with h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  rcases p1577_3 (m.d 0 3) (by simp) with h1579 | h1579
                  · rcases p1577_3 (m.d 1 3) (by simp) with h1580 | h1580
                    · linarith only [h1, h1580, hlam]
                    · rcases p1577_3 (m.d 2 3) (by simp) with h1582 | h1582
                      · linarith only [h1582, h4, hlam]
                      · linarith only [h1582, h9, hlam]
                  · linarith only [h1, h1579, hlam]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  rcases p1577_3 (m.d 0 3) (by simp) with h1586 | h1586
                  · rcases p1577_3 (m.d 1 3) (by simp) with h1587 | h1587
                    · linarith only [h1, h1587, hlam]
                    · rcases p1577_3 (m.d 2 3) (by simp) with h1589 | h1589
                      · linarith only [h1589, h4, hlam]
                      · rcases p1577_3 (m.d 3 4) (by simp) with h1591 | h1591
                        · linarith only [h1591, h6, hlam]
                        · linarith only [h1572, h1591, hlam]
                  · linarith only [h1586, h4, hlam]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h0, h1572, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1570, h1572, h6, h9, hlam, p1577_2]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h9, hlam, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1107, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1572, h6, h9, hc03, hc35, hlam, hphi, ht0b, ht5b, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h4, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1572, h6, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1572, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h0, h1572, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h6, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h0, h1570, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1577_1]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  rcases p1577_3 (m.d 0 3) (by simp) with h1611 | h1611
                  · rcases p1577_3 (m.d 1 3) (by simp) with h1612 | h1612
                    · linarith only [h1107, h1612, hlam]
                    · linarith only [h1570, h1612, hlam]
                  · linarith only [h1611, h7, hlam]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h7, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1570, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1574, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [h1576, hlam, p1577_0]
                · have p1577_0 := h1577c.1
                  have p1577_1 := h1577c.2.1
                  have p1577_2 := h1577c.2.2.1
                  have p1577_3 := h1577c.2.2.2
                  linarith only [hlam, p1577_0]
              · linarith only [h0, h1107, h1570, h1576, h4, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h1571, h1575, h969, hlam]
          · linarith only [h1, h1570, h1574, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · linarith only [h1107, h1570, h1571, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1625 | h1625
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1626 | h1626
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1627 | h1627
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1629 | h1629
              · rcases h3bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  rcases p1630_3 (m.d 0 3) (by simp) with h1632 | h1632
                  · rcases p1630_3 (m.d 1 3) (by simp) with h1633 | h1633
                    · linarith only [h1, h1633, hlam]
                    · rcases p1630_3 (m.d 2 3) (by simp) with h1635 | h1635
                      · linarith only [h1635, h4, hlam]
                      · linarith only [h1635, h9, hlam]
                  · linarith only [h1, h1632, hlam]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1570, h1626, h1629, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  rcases p1630_3 (m.d 0 3) (by simp) with h1640 | h1640
                  · rcases p1630_3 (m.d 1 3) (by simp) with h1641 | h1641
                    · linarith only [h1, h1641, hlam]
                    · rcases p1630_3 (m.d 2 3) (by simp) with h1643 | h1643
                      · linarith only [h1643, h4, hlam]
                      · linarith only [h1626, h1643, hlam]
                  · linarith only [h1640, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  rcases p1630_3 (m.d 0 3) (by simp) with h1647 | h1647
                  · rcases p1630_3 (m.d 1 3) (by simp) with h1648 | h1648
                    · linarith only [h1, h1648, hlam]
                    · rcases p1630_3 (m.d 2 3) (by simp) with h1650 | h1650
                      · linarith only [h1650, h4, hlam]
                      · linarith only [h1627, h1650, hlam]
                  · linarith only [h1647, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h9, hlam, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1107, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1570, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h4, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  rcases p1630_3 (m.d 0 3) (by simp) with h1660 | h1660
                  · rcases p1630_3 (m.d 1 3) (by simp) with h1661 | h1661
                    · linarith only [h1661, h9, hlam]
                    · rcases p1630_3 (m.d 2 3) (by simp) with h1663 | h1663
                      · rcases p1630_3 (m.d 3 4) (by simp) with h1664 | h1664
                        · linarith only [h1626, h1664, hlam]
                        · linarith only [h1107, h1664, hlam]
                      · linarith only [h1663, h9, hlam]
                  · linarith only [h1, h1660, hlam]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1570, h1629, h9, hc12, hc23, hlam, hphi, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h0, h1570, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h6, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h0, h1626, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1626, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h0, h1570, h1626, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h7, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h0, h1627, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1630_1]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1627, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [h1629, hlam, p1630_0]
                · have p1630_0 := h1630c.1
                  have p1630_1 := h1630c.2.1
                  have p1630_2 := h1630c.2.2.1
                  have p1630_3 := h1630c.2.2.2
                  linarith only [hlam, p1630_0]
              · linarith only [h1107, h1625, h1629, hlam]
            · linarith only [h0, h1107, h1625, h1626, h1628, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1107, h1625, h1626, h1627, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1685 | h1685
          · linarith only [h1570, h1626, h1685, h9, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1687 | h1687
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1688 | h1688
              · rcases h3bigk with h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  rcases p1689_3 (m.d 0 3) (by simp) with h1691 | h1691
                  · rcases p1689_3 (m.d 1 3) (by simp) with h1692 | h1692
                    · linarith only [h1, h1692, hlam]
                    · rcases p1689_3 (m.d 2 3) (by simp) with h1694 | h1694
                      · linarith only [h1694, h4, hlam]
                      · linarith only [h1694, h9, hlam]
                  · linarith only [h1, h1691, hlam]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  rcases p1689_3 (m.d 0 3) (by simp) with h1698 | h1698
                  · rcases p1689_3 (m.d 1 3) (by simp) with h1699 | h1699
                    · linarith only [h1, h1699, hlam]
                    · rcases p1689_3 (m.d 2 3) (by simp) with h1701 | h1701
                      · linarith only [h1701, h4, hlam]
                      · rcases p1689_3 (m.d 3 4) (by simp) with h1703 | h1703
                        · linarith only [h1703, h6, hlam]
                        · linarith only [h1626, h1703, hlam]
                  · linarith only [h1698, h4, hlam]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1685, h1688, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1685, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h9, hlam, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1107, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1570, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h4, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1685, h1688, hc13, hc34, hlam, hphi, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1626, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1685, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h6, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  rcases p1689_3 (m.d 0 3) (by simp) with h1720 | h1720
                  · rcases p1689_3 (m.d 1 3) (by simp) with h1721 | h1721
                    · linarith only [h1721, hlam, p1689_0]
                    · rcases p1689_3 (m.d 2 3) (by simp) with h1723 | h1723
                      · linarith only [h1626, h1723, hlam]
                      · linarith only [h1723, h9, hlam]
                  · linarith only [h1, h1720, hlam]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1570, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h7, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  rcases p1689_3 (m.d 0 3) (by simp) with h1731 | h1731
                  · rcases p1689_3 (m.d 1 3) (by simp) with h1732 | h1732
                    · linarith only [h1732, hlam, p1689_0]
                    · rcases p1689_3 (m.d 2 3) (by simp) with h1734 | h1734
                      · linarith only [h1685, h1734, hlam]
                      · linarith only [h1734, h9, hlam]
                  · linarith only [h1, h1731, hlam]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h9, hc12, hc35, hlam, hphi, ht23, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1688, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
              · linarith only [h1107, h1625, h1688, h9, h969, hc12, hc24, hlam, hphi]
            · linarith only [h1625, h1687, h969, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1743 | h1743
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1744 | h1744
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1745 | h1745
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1746 | h1746
              · linarith only [h0, h1625, h1743, h1746, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1107, h1743, h1745, h1746, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1749 | h1749
              · linarith only [h0, h1745, h1749, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases h3bigk with h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1107, h1743, h1745, h6, h8, hlam, p1751_2]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1570, h1744, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  rcases p1751_3 (m.d 0 3) (by simp) with h1755 | h1755
                  · rcases p1751_3 (m.d 1 3) (by simp) with h1756 | h1756
                    · linarith only [h1, h1756, hlam]
                    · rcases p1751_3 (m.d 2 3) (by simp) with h1758 | h1758
                      · linarith only [h1758, h4, hlam]
                      · linarith only [h1743, h1758, hlam]
                  · linarith only [h1755, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  rcases p1751_3 (m.d 0 3) (by simp) with h1762 | h1762
                  · rcases p1751_3 (m.d 1 3) (by simp) with h1763 | h1763
                    · linarith only [h1, h1763, hlam]
                    · rcases p1751_3 (m.d 2 3) (by simp) with h1765 | h1765
                      · linarith only [h1765, h4, hlam]
                      · linarith only [h1744, h1765, hlam]
                  · linarith only [h1762, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h9, hlam, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1107, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1570, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h4, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  rcases p1751_3 (m.d 0 3) (by simp) with h1775 | h1775
                  · rcases p1751_3 (m.d 1 3) (by simp) with h1776 | h1776
                    · linarith only [h1776, h9, hlam]
                    · rcases p1751_3 (m.d 2 3) (by simp) with h1778 | h1778
                      · rcases p1751_3 (m.d 3 4) (by simp) with h1779 | h1779
                        · linarith only [h1743, h1779, hlam]
                        · linarith only [h1107, h1779, hlam]
                      · linarith only [h1778, h9, hlam]
                  · linarith only [h1, h1775, hlam]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1107, h9, hc12, hc23, hlam, hphi, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h0, h1107, h1749, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h6, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1743, h1745, h8, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1743, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1749, hlam, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h7, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h0, h1744, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h1744, hlam, p1751_0]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [h0, h1744, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1751_1]
                · have p1751_0 := h1751c.1
                  have p1751_1 := h1751c.2.1
                  have p1751_2 := h1751c.2.2.1
                  have p1751_3 := h1751c.2.2.2
                  linarith only [hlam, p1751_0]
          · linarith only [h0, h1107, h1743, h1744, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1798 | h1798
          · linarith only [h1570, h1743, h1798, h9, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1800 | h1800
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1801 | h1801
              · rcases h3bigk with h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c | h1802c
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1107, h1625, h1743, h1800, h6, hlam, p1802_2]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  rcases p1802_3 (m.d 0 3) (by simp) with h1805 | h1805
                  · rcases p1802_3 (m.d 1 3) (by simp) with h1806 | h1806
                    · linarith only [h1, h1806, hlam]
                    · rcases p1802_3 (m.d 2 3) (by simp) with h1808 | h1808
                      · linarith only [h1808, h4, hlam]
                      · rcases p1802_3 (m.d 3 4) (by simp) with h1810 | h1810
                        · linarith only [h1810, h6, hlam]
                        · linarith only [h1743, h1810, hlam]
                  · linarith only [h1805, h4, hlam]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h0, h1107, h1625, h1743, h1800, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h0, h1798, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h9, hlam, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1107, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1570, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h4, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1798, hc13, hc35, hlam, hphi, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1743, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1798, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h6, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  rcases p1802_3 (m.d 0 3) (by simp) with h1827 | h1827
                  · rcases p1802_3 (m.d 1 3) (by simp) with h1828 | h1828
                    · linarith only [h1828, hlam, p1802_0]
                    · rcases p1802_3 (m.d 2 3) (by simp) with h1830 | h1830
                      · linarith only [h1743, h1830, hlam]
                      · linarith only [h1830, h9, hlam]
                  · linarith only [h1, h1827, hlam]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h0, h1570, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h7, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  rcases p1802_3 (m.d 0 3) (by simp) with h1838 | h1838
                  · rcases p1802_3 (m.d 1 3) (by simp) with h1839 | h1839
                    · linarith only [h1839, hlam, p1802_0]
                    · rcases p1802_3 (m.d 2 3) (by simp) with h1841 | h1841
                      · linarith only [h1798, h1841, hlam]
                      · linarith only [h1841, h9, hlam]
                  · linarith only [h1, h1838, hlam]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h9, hc12, hc35, hlam, hphi, ht23, p1802_1]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [h1801, hlam, p1802_0]
                · have p1802_0 := h1802c.1
                  have p1802_1 := h1802c.2.1
                  have p1802_2 := h1802c.2.2.1
                  have p1802_3 := h1802c.2.2.2
                  linarith only [hlam, p1802_0]
              · linarith only [h1107, h1800, h1801, h9, hc12, hc24, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1849 | h1849
              · linarith only [h0, h1800, h1849, h4, h6, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1743, h1849, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h969 | h969
  · exact r1l7_13_24_L_I_H_I_s7_x0_x1_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h969
  · exact r1l7_13_24_L_I_H_I_s7_x0_x1_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h969

set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · exact r1l7_13_24_L_I_H_I_s7_x0_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9
  · exact r1l7_13_24_L_I_H_I_s7_x0_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9

end R2N4
