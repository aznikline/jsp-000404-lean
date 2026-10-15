import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h1139 | h1139
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1140 | h1140
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1141 | h1141
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1142 | h1142
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1143 | h1143
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1144 | h1144
            · linarith only [h1144, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1146 | h1146
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1147 | h1147
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1148 | h1148
                  · linarith only [h1140, h1148, h2, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
                    · linarith only [h1140, h1146, h1150, h2, h9, hlam]
                    · rcases h2bigk with h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, h1139, h1147, h1150, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, h1147, h1150, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        rcases p1152_3 (m.d 0 2) (by simp) with h1156 | h1156
                        · rcases p1152_3 (m.d 1 2) (by simp) with h1157 | h1157
                          · linarith only [h0, h1157, hlam]
                          · linarith only [h1140, h1157, hlam]
                        · linarith only [h1156, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        rcases p1152_3 (m.d 0 2) (by simp) with h1161 | h1161
                        · rcases p1152_3 (m.d 1 2) (by simp) with h1162 | h1162
                          · linarith only [h0, h1162, hlam]
                          · linarith only [h1141, h1162, hlam]
                        · linarith only [h1161, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, hlam, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1147, h1150, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, h1146, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h4, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1139, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1, h1139, h1146, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, h1139, hc01, hc25, hlam, hphi, ht0b, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h5, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1140, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1146, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1148, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h6, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1141, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h1147, hlam, p1152_0]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [h0, h1146, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1152_1]
                      · have p1152_0 := h1152c.1
                        have p1152_1 := h1152c.2.1
                        have p1152_2 := h1152c.2.2.1
                        have p1152_3 := h1152c.2.2.2
                        linarith only [hlam, p1152_0]
                · linarith only [h0, h1139, h1143, h1146, h1147, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1187 | h1187
                · linarith only [h0, h1139, h1142, h1146, h1187, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1189 | h1189
                  · linarith only [h0, h1142, h1146, h1189, h2, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1191 | h1191
                    · linarith only [h1142, h1191, h2, h9, hlam]
                    · rcases h2bigk with h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, h1139, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        rcases p1193_3 (m.d 0 2) (by simp) with h1196 | h1196
                        · rcases p1193_3 (m.d 1 2) (by simp) with h1197 | h1197
                          · linarith only [h0, h1197, hlam]
                          · linarith only [h1139, h1197, hlam]
                        · linarith only [h1196, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        rcases p1193_3 (m.d 0 2) (by simp) with h1201 | h1201
                        · rcases p1193_3 (m.d 1 2) (by simp) with h1202 | h1202
                          · linarith only [h0, h1202, hlam]
                          · linarith only [h1140, h1202, hlam]
                        · linarith only [h1201, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        rcases p1193_3 (m.d 0 2) (by simp) with h1206 | h1206
                        · rcases p1193_3 (m.d 1 2) (by simp) with h1207 | h1207
                          · linarith only [h0, h1207, hlam]
                          · linarith only [h1141, h1207, hlam]
                        · linarith only [h1206, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, hlam, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h4, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h1139, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h1146, hlam, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h1187, hlam, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h5, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h1140, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h1189, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h6, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h1141, hlam, p1193_0]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [h0, h1139, h1143, h1187, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1193_1]
                      · have p1193_0 := h1193c.1
                        have p1193_1 := h1193c.2.1
                        have p1193_2 := h1193c.2.2.1
                        have p1193_3 := h1193c.2.2.2
                        linarith only [hlam, p1193_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1231 | h1231
            · linarith only [h1142, h1143, h1231, h2, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1234 | h1234
                · linarith only [h1139, h1143, h1234, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1236 | h1236
                  · linarith only [h1236, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                    · linarith only [h1139, h1143, h1233, h1238, h8, h9, hlam]
                    · rcases h2bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h0, h1139, h1233, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h0, h1233, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        rcases p1240_3 (m.d 0 2) (by simp) with h1244 | h1244
                        · rcases p1240_3 (m.d 1 2) (by simp) with h1245 | h1245
                          · linarith only [h0, h1245, hlam]
                          · linarith only [h1140, h1245, hlam]
                        · linarith only [h1244, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h0, h1233, h1234, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h0, hlam, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1233, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h0, h1233, h1234, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h4, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1139, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1139, h1143, h8, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1234, hlam, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h5, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1140, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1233, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1236, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h6, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1141, hlam, p1240_0]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1233, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [h1141, h1233, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1240_1]
                      · have p1240_0 := h1240c.1
                        have p1240_1 := h1240c.2.1
                        have p1240_2 := h1240c.2.2.1
                        have p1240_3 := h1240c.2.2.2
                        linarith only [hlam, p1240_0]
              · linarith only [h0, h1142, h1143, h1233, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1271 | h1271
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1272 | h1272
            · linarith only [h1142, h1271, h1272, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1142, h1271, h1272, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1275 | h1275
            · linarith only [h1275, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1277 | h1277
              · linarith only [h1139, h1142, h1277, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                · linarith only [h1139, h1271, h1279, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1281 | h1281
                  · linarith only [h0, h1139, h1142, h1281, h5, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1283 | h1283
                    · linarith only [h1283, h7, h9, hlam]
                    · rcases h2bigk with h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, h1139, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        rcases p1285_3 (m.d 0 2) (by simp) with h1288 | h1288
                        · rcases p1285_3 (m.d 1 2) (by simp) with h1289 | h1289
                          · linarith only [h0, h1289, hlam]
                          · linarith only [h1139, h1289, hlam]
                        · linarith only [h1288, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        rcases p1285_3 (m.d 0 2) (by simp) with h1293 | h1293
                        · rcases p1285_3 (m.d 1 2) (by simp) with h1294 | h1294
                          · linarith only [h0, h1294, hlam]
                          · linarith only [h1140, h1294, hlam]
                        · linarith only [h1293, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        rcases p1285_3 (m.d 0 2) (by simp) with h1298 | h1298
                        · rcases p1285_3 (m.d 1 2) (by simp) with h1299 | h1299
                          · linarith only [h0, h1299, hlam]
                          · linarith only [h1141, h1299, hlam]
                        · linarith only [h1298, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, hlam, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, h1277, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, h1277, h1281, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h4, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h1139, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h1277, hlam, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h1279, hlam, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h5, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h1140, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h1281, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h6, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h1141, hlam, p1285_0]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [h0, h1141, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1285_1]
                      · have p1285_0 := h1285c.1
                        have p1285_1 := h1285c.2.1
                        have p1285_2 := h1285c.2.2.1
                        have p1285_3 := h1285c.2.2.2
                        linarith only [hlam, p1285_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1323 | h1323
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1324 | h1324
          · linarith only [h1139, h1141, h1324, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1326 | h1326
            · linarith only [h1139, h1141, h1323, h1326, h6, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1328 | h1328
              · linarith only [h1139, h1141, h1328, h6, h9, hc34, hc45, hlam, hphi]
              · linarith only [h1323, h1324, h1328, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1331 | h1331
          · linarith only [h1139, h1141, h1323, h1331, h7, h9, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1333 | h1333
            · linarith only [h0, h1140, h1323, h1333, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1335 | h1335
              · linarith only [h1139, h1323, h1335, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1337 | h1337
                · linarith only [h0, h1140, h1141, h1331, h1335, h1337, h6, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1339 | h1339
                  · linarith only [h0, h1140, h1141, h1337, h1339, h4, h8, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1341 | h1341
                    · linarith only [h1140, h1141, h1337, h1341, h7, h8, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h2bigk with h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h1140, h1335, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        rcases p1343_3 (m.d 0 2) (by simp) with h1346 | h1346
                        · rcases p1343_3 (m.d 1 2) (by simp) with h1347 | h1347
                          · linarith only [h0, h1347, hlam]
                          · linarith only [h1139, h1347, hlam]
                        · linarith only [h1346, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        rcases p1343_3 (m.d 0 2) (by simp) with h1351 | h1351
                        · rcases p1343_3 (m.d 1 2) (by simp) with h1352 | h1352
                          · linarith only [h0, h1352, hlam]
                          · linarith only [h1140, h1352, hlam]
                        · linarith only [h1351, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h1140, h1141, h1335, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, hlam, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1141, h1337, h8, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h1141, h1335, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1141, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h4, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1139, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1335, hlam, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1337, hlam, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h5, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1140, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h1339, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h6, hlam, p1343_0]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h1337, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [h0, h1335, h1337, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                      · have p1343_0 := h1343c.1
                        have p1343_1 := h1343c.2.1
                        have p1343_2 := h1343c.2.2.1
                        have p1343_3 := h1343c.2.2.2
                        linarith only [hlam, p1343_0]
    · linarith only [h1139, h1140, h5, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1378 | h1378
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1379 | h1379
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1380 | h1380
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1381 | h1381
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1382 | h1382
            · linarith only [h1382, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1384 | h1384
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1385 | h1385
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1386 | h1386
                  · linarith only [h1378, h1386, h2, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1388 | h1388
                    · linarith only [h1378, h1384, h1388, h2, h9, hlam]
                    · rcases h2bigk with h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c | h1390c
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, h1379, hc01, hc25, hlam, hphi, ht0b, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, h1139, h1379, h1385, hc01, hc35, hlam, hphi, ht0b, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        rcases p1390_3 (m.d 0 2) (by simp) with h1394 | h1394
                        · rcases p1390_3 (m.d 1 2) (by simp) with h1395 | h1395
                          · linarith only [h0, h1395, hlam]
                          · linarith only [h1378, h1395, hlam]
                        · linarith only [h1394, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        rcases p1390_3 (m.d 0 2) (by simp) with h1399 | h1399
                        · rcases p1390_3 (m.d 1 2) (by simp) with h1400 | h1400
                          · linarith only [h0, h1400, hlam]
                          · linarith only [h1379, h1400, hlam]
                        · linarith only [h1399, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, hlam, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1139, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1139, h1384, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, h1139, h1384, h1386, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h4, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, h1384, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h0, h1384, h1386, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h5, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1378, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1384, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1386, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h6, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1379, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1385, hlam, p1390_0]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [h1379, h1384, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1390_1]
                      · have p1390_0 := h1390c.1
                        have p1390_1 := h1390c.2.1
                        have p1390_2 := h1390c.2.2.1
                        have p1390_3 := h1390c.2.2.2
                        linarith only [hlam, p1390_0]
                · linarith only [h0, h1139, h1379, h1385, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1139, h1378, h1384, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1139, h1379, h1381, hlam]
        · linarith only [h1139, h1378, h1380, h7, h9, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1428 | h1428
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1429 | h1429
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1430 | h1430
            · linarith only [h1430, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1432 | h1432
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1433 | h1433
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1434 | h1434
                  · linarith only [h1378, h1379, h1433, h1434, h4, h9, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1436 | h1436
                    · linarith only [h1378, h1379, h1432, h1436, h6, h9, hlam]
                    · rcases h2bigk with h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, h1378, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, h1378, h1379, h1432, h1433, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        rcases p1438_3 (m.d 0 2) (by simp) with h1442 | h1442
                        · rcases p1438_3 (m.d 1 2) (by simp) with h1443 | h1443
                          · linarith only [h0, h1443, hlam]
                          · linarith only [h1378, h1443, hlam]
                        · linarith only [h1442, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, h1378, h1379, h1432, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, hlam, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1139, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1379, h1432, h1433, h4, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1379, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h4, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, h1432, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h0, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h5, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1378, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1432, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1434, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h6, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1378, h1432, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1433, hlam, p1438_0]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [h1432, h6, h9, hc34, hc45, hlam, hphi, p1438_1]
                      · have p1438_0 := h1438c.1
                        have p1438_1 := h1438c.2.1
                        have p1438_2 := h1438c.2.2.1
                        have p1438_3 := h1438c.2.2.2
                        linarith only [hlam, p1438_0]
                · linarith only [h0, h1139, h1378, h1432, h1433, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1139, h1378, h1432, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
            · linarith only [h1470, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1472 | h1472
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                · linarith only [h0, h1139, h1378, h1429, h1472, h1473, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1139, h1378, h1472, h1473, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1139, h1378, h1472, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1139, h1378, h1428, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1478 | h1478
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1479 | h1479
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1480 | h1480
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1481 | h1481
            · linarith only [h1378, h1478, h1481, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1378, h1478, h1481, hlam]
          · linarith only [h1139, h1478, h1480, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1485 | h1485
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1486 | h1486
            · linarith only [h1139, h1478, h1479, h1486, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1378, h1478, h1486, hlam]
          · linarith only [h1139, h1478, h1485, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1490 | h1490
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1491 | h1491
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1492 | h1492
            · linarith only [h1492, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1494 | h1494
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1495 | h1495
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1496 | h1496
                  · linarith only [h1496, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1498 | h1498
                    · linarith only [h1378, h1498, h5, h9, hc12, hc34, hlam, hphi, ht23]
                    · rcases h2bigk with h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c | h1500c
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        rcases p1500_3 (m.d 0 2) (by simp) with h1502 | h1502
                        · rcases p1500_3 (m.d 1 2) (by simp) with h1503 | h1503
                          · linarith only [h0, h1503, hlam]
                          · rcases p1500_3 (m.d 2 3) (by simp) with h1505 | h1505
                            · linarith only [h1505, h4, hlam]
                            · linarith only [h1139, h1505, hlam]
                        · linarith only [h0, h1502, hlam]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, h1139, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, h1378, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, h1378, h1496, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, hlam, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h1139, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h1378, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h1478, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h4, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, h1378, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, h1378, h1496, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h5, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h1494, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h1496, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h6, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h1495, hlam, p1500_0]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [h0, h1495, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1500_1]
                      · have p1500_0 := h1500c.1
                        have p1500_1 := h1500c.2.1
                        have p1500_2 := h1500c.2.2.1
                        have p1500_3 := h1500c.2.2.2
                        linarith only [hlam, p1500_0]
                · linarith only [h1, h1139, h1491, h1495, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1139, h1494, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1534 | h1534
            · linarith only [h1534, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1536 | h1536
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1537 | h1537
                · linarith only [h0, h1490, h1491, h1537, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1539 | h1539
                  · linarith only [h1539, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1541 | h1541
                    · linarith only [h1378, h1490, h1536, h1537, h1541, h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c | h1543c
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        rcases p1543_3 (m.d 0 2) (by simp) with h1545 | h1545
                        · rcases p1543_3 (m.d 1 2) (by simp) with h1546 | h1546
                          · linarith only [h0, h1546, hlam]
                          · rcases p1543_3 (m.d 2 3) (by simp) with h1548 | h1548
                            · linarith only [h1548, h4, hlam]
                            · linarith only [h1139, h1548, hlam]
                        · linarith only [h0, h1545, hlam]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, h1378, h1536, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, h1378, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, h1478, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, hlam, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1139, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1378, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1478, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h4, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1537, h8, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, h1378, h1537, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1537, hlam, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h5, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1536, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h1539, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h6, hlam, p1543_0]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, h1139, h1537, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [h0, h1378, h1537, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1543_1]
                      · have p1543_0 := h1543c.1
                        have p1543_1 := h1543c.2.1
                        have p1543_2 := h1543c.2.2.1
                        have p1543_3 := h1543c.2.2.2
                        linarith only [hlam, p1543_0]
              · linarith only [h1, h1139, h1490, h1536, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1576 | h1576
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1577 | h1577
            · linarith only [h1378, h1577, h5, h9, hlam]
            · linarith only [h1490, h1576, h1577, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1580 | h1580
            · linarith only [h1490, h1580, h2, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1582 | h1582
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1583 | h1583
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1584 | h1584
                  · linarith only [h1584, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1586 | h1586
                    · linarith only [h1582, h1586, h5, h9, hlam]
                    · rcases h2bigk with h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c | h1588c
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        rcases p1588_3 (m.d 0 2) (by simp) with h1590 | h1590
                        · rcases p1588_3 (m.d 1 2) (by simp) with h1591 | h1591
                          · linarith only [h0, h1591, hlam]
                          · rcases p1588_3 (m.d 2 3) (by simp) with h1593 | h1593
                            · linarith only [h1593, h4, hlam]
                            · linarith only [h1139, h1593, hlam]
                        · linarith only [h0, h1590, hlam]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, h1139, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, h1139, h1490, h1582, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, h1478, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, hlam, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h1139, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h1378, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h1478, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h4, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, h1139, h1490, h1582, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, h1478, h1580, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h5, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h1582, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h1584, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h6, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h1583, hlam, p1588_0]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [h0, h1583, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1588_1]
                      · have p1588_0 := h1588c.1
                        have p1588_1 := h1588c.2.1
                        have p1588_2 := h1588c.2.2.1
                        have p1588_3 := h1588c.2.2.2
                        linarith only [hlam, p1588_0]
                · linarith only [h0, h1139, h1490, h1582, h1583, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1139, h1582, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h1622 | h1622
  · linarith only [h1622, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1624 | h1624
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1625 | h1625
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1626 | h1626
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1627 | h1627
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1628 | h1628
            · linarith only [h1, h1628, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1630 | h1630
              · linarith only [h1622, h1630, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1632 | h1632
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1633 | h1633
                  · linarith only [h1, h1624, h1633, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1635 | h1635
                    · linarith only [h1622, h1625, h1635, h2, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1637 | h1637
                      · linarith only [h1622, h1626, h1632, h1633, h1637, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1626, h1633, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1632, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          rcases p1639_3 (m.d 0 2) (by simp) with h1643 | h1643
                          · rcases p1639_3 (m.d 1 2) (by simp) with h1644 | h1644
                            · linarith only [h0, h1644, hlam]
                            · linarith only [h1625, h1644, hlam]
                          · linarith only [h1643, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1632, h1633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, hlam, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1632, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1632, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1632, h1633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h4, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1624, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1632, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1633, hlam, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h5, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1625, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1632, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1635, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h6, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h1626, hlam, p1639_0]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [h0, h1626, h1632, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1639_1]
                        · have p1639_0 := h1639c.1
                          have p1639_1 := h1639c.2.1
                          have p1639_2 := h1639c.2.2.1
                          have p1639_3 := h1639c.2.2.2
                          linarith only [hlam, p1639_0]
                · linarith only [h1632, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1627, h7, h8, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1671 | h1671
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1672 | h1672
            · linarith only [h1624, h1626, h1672, h6, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1674 | h1674
              · linarith only [h1622, h1674, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1676 | h1676
                · linarith only [h0, h1624, h1626, h1676, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1676, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1671, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1624, h1625, h5, h7, h8, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1681 | h1681
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1682 | h1682
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1683 | h1683
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1684 | h1684
            · linarith only [h1624, h1681, h1684, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1624, h1682, h1684, hlam]
          · linarith only [h1624, h1681, h1683, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1688 | h1688
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1689 | h1689
            · linarith only [h1, h1689, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1691 | h1691
              · linarith only [h1622, h1624, h1681, h1691, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1693 | h1693
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1694 | h1694
                  · linarith only [h1694, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1696 | h1696
                    · linarith only [h1622, h1696, h5, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1698 | h1698
                      · linarith only [h1622, h1624, h1681, h1693, h1698, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1624, h1681, h1693, h1698, h4, h8, hc34, hc45, hlam, hphi]
                · linarith only [h1624, h1681, h1693, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h1688, h7, h8, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1703 | h1703
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1704 | h1704
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1705 | h1705
            · linarith only [h1, h1705, h8, hlam]
            · linarith only [h1624, h1703, h1705, hlam]
          · linarith only [h1624, h1703, h1704, h7, h8, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1709 | h1709
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1710 | h1710
            · linarith only [h1, h1710, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1712 | h1712
              · linarith only [h1622, h1681, h1712, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1714 | h1714
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1715 | h1715
                  · linarith only [h1715, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1717 | h1717
                    · linarith only [h1622, h1717, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1719 | h1719
                      · linarith only [h1622, h1681, h1719, h5, hc12, hc34, hlam, hphi, ht23]
                      · rcases h2bigk with h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          rcases p1721_3 (m.d 0 2) (by simp) with h1723 | h1723
                          · rcases p1721_3 (m.d 1 2) (by simp) with h1724 | h1724
                            · linarith only [h0, h1724, hlam]
                            · rcases p1721_3 (m.d 2 3) (by simp) with h1726 | h1726
                              · linarith only [h1726, h4, hlam]
                              · linarith only [h1624, h1726, hlam]
                          · linarith only [h0, h1723, hlam]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h0, h1624, h1709, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h0, h1681, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h0, h1703, h1709, h1710, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h0, hlam, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1624, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1681, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1703, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h4, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1681, h4, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1715, hlam, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h5, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1714, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h1717, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h6, hlam, p1721_0]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [h0, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1721_1]
                        · have p1721_0 := h1721c.1
                          have p1721_1 := h1721c.2.1
                          have p1721_2 := h1721c.2.2.1
                          have p1721_3 := h1721c.2.2.2
                          linarith only [hlam, p1721_0]
                · linarith only [h1, h1624, h1709, h1714, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1709, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8

end R2N4
