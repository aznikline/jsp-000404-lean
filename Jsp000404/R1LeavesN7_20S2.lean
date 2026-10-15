import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h1092 | h1092
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1093 | h1093
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1094 | h1094
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1095 | h1095
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1096 | h1096
          · linarith only [h1, h1096, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1098 | h1098
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1099 | h1099
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1100 | h1100
                · linarith only [h1, h1093, h1100, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1102 | h1102
                  · linarith only [h1092, h1098, h1102, h6, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h2bigk with h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1092, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1099, hc01, hc35, hlam, hphi, ht0b, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      rcases p1104_3 (m.d 0 2) (by simp) with h1108 | h1108
                      · rcases p1104_3 (m.d 1 2) (by simp) with h1109 | h1109
                        · linarith only [h0, h1109, hlam]
                        · linarith only [h1093, h1109, hlam]
                      · linarith only [h1108, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      rcases p1104_3 (m.d 0 2) (by simp) with h1113 | h1113
                      · rcases p1104_3 (m.d 1 2) (by simp) with h1114 | h1114
                        · linarith only [h0, h1114, hlam]
                        · linarith only [h1094, h1114, hlam]
                      · linarith only [h1113, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1099, h1102, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1098, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h2, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1092, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1098, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1092, hc01, hc25, hlam, hphi, ht0b, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h3, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1093, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1098, hlam, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1100, hlam, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h4, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1094, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1099, hlam, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1098, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1138 | h1138
                · linarith only [h1, h1093, h1138, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1140 | h1140
                  · linarith only [h1, h1093, h1098, h1140, h6, hlam]
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
                      linarith only [h0, h1094, hc01, hc25, hlam, hphi, ht0b, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, h1098, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      rcases p1142_3 (m.d 0 2) (by simp) with h1146 | h1146
                      · rcases p1142_3 (m.d 1 2) (by simp) with h1147 | h1147
                        · linarith only [h0, h1147, hlam]
                        · linarith only [h1093, h1147, hlam]
                      · linarith only [h1146, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, h1098, h1099, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1098, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, h1098, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, h1098, h1099, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h2, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1092, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1098, h1099, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1099, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h3, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1093, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1098, hlam, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1138, hlam, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h4, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h1094, hlam, p1142_0]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [h0, h1094, h1098, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                    · have p1142_0 := h1142c.1
                      have p1142_1 := h1142c.2.1
                      have p1142_2 := h1142c.2.2.1
                      have p1142_3 := h1142c.2.2.2
                      linarith only [hlam, p1142_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1172 | h1172
              · linarith only [h0, h1092, h1095, h1098, h1172, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1174 | h1174
                · linarith only [h0, h1092, h1095, h1098, h1174, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h1, h1095, h1176, h6, hlam]
                  · rcases h2bigk with h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, h1092, h1095, h1098, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      rcases p1178_3 (m.d 0 2) (by simp) with h1181 | h1181
                      · rcases p1178_3 (m.d 1 2) (by simp) with h1182 | h1182
                        · linarith only [h0, h1182, hlam]
                        · linarith only [h1092, h1182, hlam]
                      · linarith only [h1181, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      rcases p1178_3 (m.d 0 2) (by simp) with h1186 | h1186
                      · rcases p1178_3 (m.d 1 2) (by simp) with h1187 | h1187
                        · linarith only [h0, h1187, hlam]
                        · linarith only [h1093, h1187, hlam]
                      · linarith only [h1186, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      rcases p1178_3 (m.d 0 2) (by simp) with h1191 | h1191
                      · rcases p1178_3 (m.d 1 2) (by simp) with h1192 | h1192
                        · linarith only [h0, h1192, hlam]
                        · linarith only [h1094, h1192, hlam]
                      · linarith only [h1191, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h2, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h1092, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h1098, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h1172, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h3, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h1093, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h1174, hlam, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h4, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h1094, hlam, p1178_0]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [h0, h1094, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1178_1]
                    · have p1178_0 := h1178c.1
                      have p1178_1 := h1178c.2.1
                      have p1178_2 := h1178c.2.2.1
                      have p1178_3 := h1178c.2.2.2
                      linarith only [hlam, p1178_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1216 | h1216
          · linarith only [h1095, h1216, h5, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1218 | h1218
            · linarith only [h0, h1092, h1095, h1218, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1220 | h1220
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1221 | h1221
                · linarith only [h1092, h1095, h1220, h1221, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h1218, h1220, h1221, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1224 | h1224
                · linarith only [h0, h1095, h1224, h3, h5, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1226 | h1226
                  · linarith only [h1226, h5, h6, hlam]
                  · rcases h2bigk with h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, h1092, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      rcases p1228_3 (m.d 0 2) (by simp) with h1231 | h1231
                      · rcases p1228_3 (m.d 1 2) (by simp) with h1232 | h1232
                        · linarith only [h0, h1232, hlam]
                        · linarith only [h1092, h1232, hlam]
                      · linarith only [h1231, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      rcases p1228_3 (m.d 0 2) (by simp) with h1236 | h1236
                      · rcases p1228_3 (m.d 1 2) (by simp) with h1237 | h1237
                        · linarith only [h0, h1237, hlam]
                        · linarith only [h1093, h1237, hlam]
                      · linarith only [h1236, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      rcases p1228_3 (m.d 0 2) (by simp) with h1241 | h1241
                      · rcases p1228_3 (m.d 1 2) (by simp) with h1242 | h1242
                        · linarith only [h0, h1242, hlam]
                        · linarith only [h1094, h1242, hlam]
                      · linarith only [h1241, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, h1218, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, h1218, h1224, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h2, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h1092, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h1218, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h1220, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h3, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h1093, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h1224, hlam, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h4, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h1094, hlam, p1228_0]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [h0, h1094, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1228_1]
                    · have p1228_0 := h1228c.1
                      have p1228_1 := h1228c.2.1
                      have p1228_2 := h1228c.2.2.1
                      have p1228_3 := h1228c.2.2.2
                      linarith only [hlam, p1228_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1266 | h1266
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1267 | h1267
          · linarith only [h1, h1092, h1094, h1266, h1267, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1269 | h1269
            · linarith only [h0, h1092, h1094, h1269, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1092, h1094, h1266, h1269, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1272 | h1272
          · linarith only [h0, h1093, h1094, h1272, h4, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1274 | h1274
            · linarith only [h1092, h1266, h1274, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1276 | h1276
              · linarith only [h0, h1092, h1094, h1276, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1278 | h1278
                · linarith only [h0, h1093, h1094, h1278, h4, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1280 | h1280
                  · linarith only [h0, h1093, h1094, h1280, h2, h4, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h2bigk with h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h1093, h1274, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      rcases p1282_3 (m.d 0 2) (by simp) with h1285 | h1285
                      · rcases p1282_3 (m.d 1 2) (by simp) with h1286 | h1286
                        · linarith only [h0, h1286, hlam]
                        · linarith only [h1092, h1286, hlam]
                      · linarith only [h1285, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      rcases p1282_3 (m.d 0 2) (by simp) with h1290 | h1290
                      · rcases p1282_3 (m.d 1 2) (by simp) with h1291 | h1291
                        · linarith only [h0, h1291, hlam]
                        · linarith only [h1093, h1291, hlam]
                      · linarith only [h1290, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h1093, h1094, h1274, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1094, h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h1094, h1274, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1094, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h2, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1092, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1274, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1276, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h3, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1093, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h1278, hlam, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h4, hlam, p1282_0]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1282_1]
                    · have p1282_0 := h1282c.1
                      have p1282_1 := h1282c.2.1
                      have p1282_2 := h1282c.2.2.1
                      have p1282_3 := h1282c.2.2.2
                      linarith only [hlam, p1282_0]
    · linarith only [h1092, h1093, h3, h6, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1317 | h1317
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1318 | h1318
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1319 | h1319
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1320 | h1320
          · linarith only [h1, h1320, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1322 | h1322
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1323 | h1323
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1324 | h1324
                · linarith only [h0, h1, h1317, h1324, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1326 | h1326
                  · linarith only [h1, h1317, h1322, h1326, h6, hlam]
                  · rcases h2bigk with h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, h1318, hc01, hc25, hlam, hphi, ht0b, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, h1092, h1318, h1323, hc01, hc35, hlam, hphi, ht0b, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      rcases p1328_3 (m.d 0 2) (by simp) with h1332 | h1332
                      · rcases p1328_3 (m.d 1 2) (by simp) with h1333 | h1333
                        · linarith only [h0, h1333, hlam]
                        · linarith only [h1317, h1333, hlam]
                      · linarith only [h1332, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      rcases p1328_3 (m.d 0 2) (by simp) with h1337 | h1337
                      · rcases p1328_3 (m.d 1 2) (by simp) with h1338 | h1338
                        · linarith only [h0, h1338, hlam]
                        · linarith only [h1318, h1338, hlam]
                      · linarith only [h1337, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1092, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1092, h1322, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, h1092, h1322, h1324, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h2, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, h1322, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h0, h1322, h1324, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h3, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1317, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1322, hlam, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1324, hlam, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h4, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1318, hlam, p1328_0]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1323, hlam, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [h1318, h1322, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1328_1]
                    · have p1328_0 := h1328c.1
                      have p1328_1 := h1328c.2.1
                      have p1328_2 := h1328c.2.2.1
                      have p1328_3 := h1328c.2.2.2
                      linarith only [hlam, p1328_0]
              · linarith only [h1092, h1318, h1323, hlam]
            · linarith only [h0, h1092, h1318, h1322, h2, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h1092, h1317, h1319, h5, h6, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1365 | h1365
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1366 | h1366
          · linarith only [h1, h1366, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1368 | h1368
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1369 | h1369
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1370 | h1370
                · linarith only [h1317, h1318, h1370, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1372 | h1372
                  · linarith only [h1317, h1318, h1368, h1372, h4, h6, hlam]
                  · rcases h2bigk with h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h1317, h1368, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h1317, h1318, h1368, h1369, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      rcases p1374_3 (m.d 0 2) (by simp) with h1378 | h1378
                      · rcases p1374_3 (m.d 1 2) (by simp) with h1379 | h1379
                        · linarith only [h0, h1379, hlam]
                        · linarith only [h1317, h1379, hlam]
                      · linarith only [h1378, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h1317, h1318, h1368, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1092, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1318, h1368, h4, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1318, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h2, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h1368, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h3, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1317, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1368, hlam, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1370, hlam, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h4, hlam, p1374_0]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1317, h1368, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h1369, hlam, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [h0, h1368, h1369, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1]
                    · have p1374_0 := h1374c.1
                      have p1374_1 := h1374c.2.1
                      have p1374_2 := h1374c.2.2.1
                      have p1374_3 := h1374c.2.2.2
                      linarith only [hlam, p1374_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1404 | h1404
                · linarith only [h1, h1317, h1404, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1406 | h1406
                  · linarith only [h1092, h1317, h1368, h1369, h1406, h4, h6, hlam]
                  · linarith only [h1092, h1317, h1369, h1406, hc24, hc45, hlam, hphi]
            · linarith only [h0, h1092, h1317, h1368, h2, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1092, h1317, h1365, h5, h6, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1411 | h1411
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1412 | h1412
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1413 | h1413
          · linarith only [h1317, h1411, h1413, h3, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1317, h1411, h1413, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1416 | h1416
          · linarith only [h1092, h1411, h1412, h1416, h5, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1317, h1411, h1416, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1419 | h1419
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1420 | h1420
          · linarith only [h1, h1420, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1422 | h1422
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1423 | h1423
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1424 | h1424
                · linarith only [h1424, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1426 | h1426
                  · linarith only [h1426, h5, h6, hlam]
                  · rcases h2bigk with h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      rcases p1428_3 (m.d 0 2) (by simp) with h1430 | h1430
                      · rcases p1428_3 (m.d 1 2) (by simp) with h1431 | h1431
                        · linarith only [h0, h1431, hlam]
                        · rcases p1428_3 (m.d 2 3) (by simp) with h1433 | h1433
                          · linarith only [h1433, h2, hlam]
                          · linarith only [h1092, h1433, hlam]
                      · linarith only [h0, h1430, hlam]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h1092, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h1317, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h1317, h1424, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h1092, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h1317, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h1411, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h2, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h1317, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h1317, h1424, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h3, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h1422, hlam, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h1424, hlam, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h4, hlam, p1428_0]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h1423, hlam, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [h0, h1423, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1428_1]
                    · have p1428_0 := h1428c.1
                      have p1428_1 := h1428c.2.1
                      have p1428_2 := h1428c.2.2.1
                      have p1428_3 := h1428c.2.2.2
                      linarith only [hlam, p1428_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1460 | h1460
                · linarith only [h1460, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1462 | h1462
                  · linarith only [h1317, h1462, h3, h6, hc12, hc34, hlam, hphi, ht23]
                  · rcases h2bigk with h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      rcases p1464_3 (m.d 0 2) (by simp) with h1466 | h1466
                      · rcases p1464_3 (m.d 1 2) (by simp) with h1467 | h1467
                        · linarith only [h0, h1467, hlam]
                        · rcases p1464_3 (m.d 2 3) (by simp) with h1469 | h1469
                          · linarith only [h1469, h2, hlam]
                          · linarith only [h1092, h1469, hlam]
                      · linarith only [h0, h1466, hlam]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1092, h1419, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1317, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1092, h1419, h1423, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1092, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1317, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1411, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h2, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1317, h1423, hc12, hc35, hlam, hphi, ht23, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1423, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h3, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1422, hlam, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1460, hlam, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h4, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1317, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
            · linarith only [h1092, h1422, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1497 | h1497
          · linarith only [h1, h1497, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1499 | h1499
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1500 | h1500
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                · linarith only [h1501, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1503 | h1503
                  · linarith only [h1499, h1503, h3, h6, hlam]
                  · rcases h2bigk with h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      rcases p1505_3 (m.d 0 2) (by simp) with h1507 | h1507
                      · rcases p1505_3 (m.d 1 2) (by simp) with h1508 | h1508
                        · linarith only [h0, h1508, hlam]
                        · rcases p1505_3 (m.d 2 3) (by simp) with h1510 | h1510
                          · linarith only [h1510, h2, hlam]
                          · linarith only [h1092, h1510, hlam]
                      · linarith only [h0, h1507, hlam]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, h1500, hc01, hc35, hlam, hphi, ht0b, ht5b, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, h1092, h1419, h1499, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, h1411, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h1092, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h1317, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h1411, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h2, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, h1092, h1419, h1499, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, h1411, h1497, h2, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h3, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h1499, hlam, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h1501, hlam, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h4, hlam, p1505_0]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h1500, hlam, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [h0, h1500, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1505_1]
                    · have p1505_0 := h1505c.1
                      have p1505_1 := h1505c.2.1
                      have p1505_2 := h1505c.2.2.1
                      have p1505_3 := h1505c.2.2.2
                      linarith only [hlam, p1505_0]
              · linarith only [h1092, h1419, h1499, h1500, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1092, h1499, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6

end R2N4
