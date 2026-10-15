import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1089 | h1089
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1090 | h1090
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1091 | h1091
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1092 | h1092
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1093 | h1093
            · linarith only [h1093, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                  · linarith only [h1088, h1095, h1097, h2, h6, hc12, hlam, hphi, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1099 | h1099
                    · linarith only [h0, h1088, h1095, h1099, h2, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h1bigk with h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1088, h1096, h1099, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1101_1]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        rcases p1101_3 (m.d 0 1) (by simp) with h1104 | h1104
                        · rcases p1101_3 (m.d 1 2) (by simp) with h1105 | h1105
                          · linarith only [h0, h1105, hlam]
                          · linarith only [h1088, h1105, hlam]
                        · linarith only [h1104, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        rcases p1101_3 (m.d 0 1) (by simp) with h1109 | h1109
                        · rcases p1101_3 (m.d 1 2) (by simp) with h1110 | h1110
                          · linarith only [h0, h1110, hlam]
                          · linarith only [h1089, h1110, hlam]
                        · linarith only [h1109, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        rcases p1101_3 (m.d 0 1) (by simp) with h1114 | h1114
                        · rcases p1101_3 (m.d 1 2) (by simp) with h1115 | h1115
                          · linarith only [h0, h1115, hlam]
                          · linarith only [h1090, h1115, hlam]
                        · linarith only [h1114, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h0, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1092, h1093, hc12, hlam, hphi, p1101_1, u1ehi3]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1101_1, u1ehi3]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h0, h1093, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1101_1, u1ehi3]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1088, hlam, p1101_1]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hc13, hlam, hphi, p1101_1, u1ehi3]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h0, h1088, h1093, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1101_1, u1ehi3]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h2, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1089, hlam, p1101_1]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1091, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1093, hlam, p1101_1]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h3, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1090, hlam, p1101_1]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [h1092, hlam, p1101_0]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hc15, hlam, hphi, p1101_1, u1ehi3]
                      · have p1101_0 := h1101c.1
                        have p1101_1 := h1101c.2.1
                        have p1101_2 := h1101c.2.2.1
                        have p1101_3 := h1101c.2.2.2
                        linarith only [hlam, p1101_0]
                · linarith only [h0, h1088, h1092, h1095, h1096, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1140 | h1140
                · linarith only [h0, h1088, h1091, h1095, h1140, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1142 | h1142
                  · linarith only [h1142, h2, h6, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1144 | h1144
                    · linarith only [h0, h1088, h1091, h1144, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1088, h1092, h1095, h1144, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1092, h1095, h1144, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        rcases p1146_3 (m.d 0 1) (by simp) with h1150 | h1150
                        · rcases p1146_3 (m.d 1 2) (by simp) with h1151 | h1151
                          · linarith only [h0, h1151, hlam]
                          · linarith only [h1089, h1151, hlam]
                        · linarith only [h1150, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        rcases p1146_3 (m.d 0 1) (by simp) with h1155 | h1155
                        · rcases p1146_3 (m.d 1 2) (by simp) with h1156 | h1156
                          · linarith only [h0, h1156, hlam]
                          · linarith only [h1090, h1156, hlam]
                        · linarith only [h1155, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h0, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1092, h1095, h1144, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1146_1, u1ehi3]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1146_1, u1ehi4]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1088, hlam, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hc13, hlam, hphi, p1146_1, u1ehi3]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h0, h1088, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1146_1, u1ehi4]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h2, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1089, hlam, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1091, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1093, hlam, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h3, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1090, hlam, p1146_1]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [h1092, hlam, p1146_0]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hc15, hlam, hphi, p1146_1, u1ehi3]
                      · have p1146_0 := h1146c.1
                        have p1146_1 := h1146c.2.1
                        have p1146_2 := h1146c.2.2.1
                        have p1146_3 := h1146c.2.2.2
                        linarith only [hlam, p1146_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1180 | h1180
            · linarith only [h1092, h1180, h5, h6, hc14, hlam, hphi, u1ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1182 | h1182
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1183 | h1183
                · linarith only [h1088, h1092, h1183, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1185 | h1185
                  · linarith only [h1185, h2, h6, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1187 | h1187
                    · linarith only [h1088, h1092, h1182, h1187, h5, h6, hlam]
                    · rcases h1bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1088, h1182, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1189_1]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        rcases p1189_3 (m.d 0 1) (by simp) with h1192 | h1192
                        · rcases p1189_3 (m.d 1 2) (by simp) with h1193 | h1193
                          · linarith only [h0, h1193, hlam]
                          · linarith only [h1088, h1193, hlam]
                        · linarith only [h1192, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        rcases p1189_3 (m.d 0 1) (by simp) with h1197 | h1197
                        · rcases p1189_3 (m.d 1 2) (by simp) with h1198 | h1198
                          · linarith only [h0, h1198, hlam]
                          · linarith only [h1089, h1198, hlam]
                        · linarith only [h1197, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        rcases p1189_3 (m.d 0 1) (by simp) with h1202 | h1202
                        · rcases p1189_3 (m.d 1 2) (by simp) with h1203 | h1203
                          · linarith only [h0, h1203, hlam]
                          · linarith only [h1090, h1203, hlam]
                        · linarith only [h1202, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h0, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1091, hc12, hlam, hphi, p1189_1, u1ehi3]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1189_1, u1ehi3]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1189_1, u1ehi4]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1088, hlam, p1189_1]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1092, h5, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1189_1, u1ehi3]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1092, hlam, p1189_1]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h2, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1089, hlam, p1189_1]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1091, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1180, hlam, p1189_1]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h3, hlam, p1189_0]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h1090, hlam, p1189_1]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [hc15, hlam, hphi, p1189_1, u1ehi2]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [h0, h1092, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1189_1, u1ehi3]
                      · have p1189_0 := h1189c.1
                        have p1189_1 := h1189c.2.1
                        have p1189_2 := h1189c.2.2.1
                        have p1189_3 := h1189c.2.2.2
                        linarith only [hlam, p1189_0]
              · linarith only [h0, h1091, h1092, h1182, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1228 | h1228
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1229 | h1229
            · linarith only [h1229, h2, h6, hlam]
            · linarith only [h1091, h1228, h1229, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1232 | h1232
            · linarith only [h1232, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1234 | h1234
              · linarith only [h1091, h1234, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1236 | h1236
                · linarith only [h1088, h1228, h1236, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1238 | h1238
                  · linarith only [h1091, h1238, h2, h6, hc24, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1240 | h1240
                    · linarith only [h1091, h1240, h2, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                    · linarith only [h1091, h1240, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1244 | h1244
          · linarith only [h1088, h1090, h1244, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1246 | h1246
            · linarith only [h1246, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1249 | h1249
                · linarith only [h1088, h1244, h1249, hc12, hlam, hphi, u1ehi2]
                · linarith only [h0, h1088, h1090, h1248, h1249, h4, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1243, h1244, h1248, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1253 | h1253
          · linarith only [h1088, h1090, h1253, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1255 | h1255
            · linarith only [h1089, h1090, h1255, h3, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1257 | h1257
              · linarith only [h1088, h1243, h1257, hc12, hlam, hphi, u1ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1259 | h1259
                · linarith only [h1089, h1090, h1253, h1257, h1259, hc25, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1261 | h1261
                  · linarith only [h0, h1089, h1090, h1259, h1261, h4, h5, h6, hc01, hc05, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1263 | h1263
                    · linarith only [h1089, h1090, h1257, h1259, h1263, h5, h6, hc23, hc34, hlam, hphi]
                    · linarith only [h1243, h1263, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1266 | h1266
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1267 | h1267
        · linarith only [h1088, h1089, h1267, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1269 | h1269
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
            · linarith only [h1270, h2, h6, hlam]
            · linarith only [h1088, h1089, h1269, h1270, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1273 | h1273
            · linarith only [h1273, h2, h6, hlam]
            · linarith only [h1089, h1266, h1273, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1276 | h1276
        · linarith only [h1088, h1089, h1276, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1278 | h1278
          · linarith only [h1088, h1266, h1278, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1280 | h1280
            · linarith only [h1280, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1282 | h1282
              · linarith only [h1276, h1282, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1284 | h1284
                · linarith only [h1088, h1278, h1284, hc12, hlam, hphi, u1ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1286 | h1286
                  · linarith only [h1282, h1286, h2, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h1088, h1089, h1286, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1289 | h1289
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1290 | h1290
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1291 | h1291
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1292 | h1292
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1293 | h1293
            · linarith only [h1293, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1295 | h1295
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1296 | h1296
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h1289, h1297, h2, h6, hc12, hlam, hphi, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1299 | h1299
                    · linarith only [h0, h1088, h1290, h1295, h1297, h1299, h2, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h1bigk with h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        rcases p1301_3 (m.d 0 1) (by simp) with h1303 | h1303
                        · rcases p1301_3 (m.d 1 2) (by simp) with h1304 | h1304
                          · linarith only [h1304, hlam, p1301_0]
                          · rcases p1301_3 (m.d 1 3) (by simp) with h1306 | h1306
                            · linarith only [h1, h1306, hlam]
                            · linarith only [h1088, h1306, hlam]
                        · linarith only [h1303, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        rcases p1301_3 (m.d 0 1) (by simp) with h1310 | h1310
                        · rcases p1301_3 (m.d 1 2) (by simp) with h1311 | h1311
                          · linarith only [h0, h1311, hlam]
                          · rcases p1301_3 (m.d 1 3) (by simp) with h1313 | h1313
                            · linarith only [h1313, hlam, p1301_0]
                            · rcases p1301_3 (m.d 1 4) (by simp) with h1315 | h1315
                              · linarith only [h1315, h2, hlam]
                              · rcases p1301_3 (m.d 1 5) (by simp) with h1317 | h1317
                                · linarith only [h1317, h3, hlam]
                                · rcases h5bigk with h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1293, h6, hc45, hlam, hphi, ht12, ht23, ht34, p1319_1, u1ehi3]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    rcases p1319_3 (m.d 0 5) (by simp) with h1322 | h1322
                                    · rcases p1319_3 (m.d 1 5) (by simp) with h1323 | h1323
                                      · linarith only [h1323, h3, hlam]
                                      · linarith only [h1290, h1323, hlam]
                                    · linarith only [h1322, hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    rcases p1319_3 (m.d 0 5) (by simp) with h1327 | h1327
                                    · rcases p1319_3 (m.d 1 5) (by simp) with h1328 | h1328
                                      · linarith only [h1328, h3, hlam]
                                      · linarith only [h1292, h1328, hlam]
                                    · linarith only [h1327, h5, hlam]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h6, hlam, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h3, hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h0, h1088, h1290, h1297, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h0, h1088, h1290, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1293, hlam, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h3, hc25, hlam, hphi, ht12, p1319_1, u1ehi4]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1290, hlam, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h0, h1088, h1290, h1299, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1297, hlam, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h5, hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1292, hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1296, hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [hlam, p1319_0]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1299, hlam, p1319_1]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h2, h6, hc45, hlam, hphi, ht12, ht23, ht34, p1319_1, u1ehi3]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [h1293, hc45, hlam, hphi, ht12, ht23, ht34, p1319_1, u1ehi3]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    rcases p1319_3 (m.d 0 5) (by simp) with h1350 | h1350
                                    · linarith only [h1350, h6, hlam]
                                    · linarith only [h0, h1088, h1290, h1350, h2, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    rcases p1319_3 (m.d 0 5) (by simp) with h1353 | h1353
                                    · linarith only [h1353, h6, hlam]
                                    · linarith only [h1353, h5, hlam]
                                  · have p1319_0 := h1319c.1
                                    have p1319_1 := h1319c.2.1
                                    have p1319_2 := h1319c.2.2.1
                                    have p1319_3 := h1319c.2.2.2
                                    linarith only [hlam, p1319_0]
                        · linarith only [h1310, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        rcases p1301_3 (m.d 0 1) (by simp) with h1358 | h1358
                        · rcases p1301_3 (m.d 1 2) (by simp) with h1359 | h1359
                          · linarith only [h0, h1359, hlam]
                          · linarith only [h1289, h1359, hlam]
                        · linarith only [h1358, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        rcases p1301_3 (m.d 0 1) (by simp) with h1363 | h1363
                        · rcases p1301_3 (m.d 1 2) (by simp) with h1364 | h1364
                          · linarith only [h0, h1364, hlam]
                          · linarith only [h1290, h1364, hlam]
                        · linarith only [h1363, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h0, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1088, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h0, h1088, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1301_1, u1ehi3]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h0, h1088, h1293, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1301_1, u1ehi3]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [hc13, hlam, hphi, p1301_1, u1ehi1]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h0, h1088, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1301_1, u1ehi3]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h0, h1088, h1293, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1301_1, u1ehi3]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h2, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1289, hlam, p1301_1]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1291, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1293, hlam, p1301_1]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h3, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1290, hlam, p1301_1]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1292, hlam, p1301_0]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [h1290, hc12, hlam, hphi, p1301_1, u1ehi3]
                      · have p1301_0 := h1301c.1
                        have p1301_1 := h1301c.2.1
                        have p1301_2 := h1301c.2.2.1
                        have p1301_3 := h1301c.2.2.2
                        linarith only [hlam, p1301_0]
                · linarith only [h1088, h1296, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1088, h1290, h1293, h1295, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · linarith only [h1088, h1290, h1292, hlam]
        · linarith only [h1088, h1289, h1291, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1392 | h1392
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1393 | h1393
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1394 | h1394
            · linarith only [h1394, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1396 | h1396
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1397 | h1397
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1398 | h1398
                  · linarith only [h1289, h1290, h1397, h1398, h6, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1400 | h1400
                    · linarith only [h0, h1289, h1290, h1396, h1397, h1400, h4, h6, hc01, hc05, hlam, hphi, ht0b, ht5b]
                    · rcases h1bigk with h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        rcases p1402_3 (m.d 0 1) (by simp) with h1404 | h1404
                        · rcases p1402_3 (m.d 1 2) (by simp) with h1405 | h1405
                          · linarith only [h1405, hlam, p1402_0]
                          · rcases p1402_3 (m.d 1 3) (by simp) with h1407 | h1407
                            · linarith only [h1, h1407, hlam]
                            · linarith only [h1088, h1407, hlam]
                        · linarith only [h1404, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        rcases p1402_3 (m.d 0 1) (by simp) with h1411 | h1411
                        · rcases p1402_3 (m.d 1 2) (by simp) with h1412 | h1412
                          · linarith only [h0, h1412, hlam]
                          · rcases p1402_3 (m.d 1 3) (by simp) with h1414 | h1414
                            · linarith only [h1414, hlam, p1402_0]
                            · rcases p1402_3 (m.d 1 4) (by simp) with h1416 | h1416
                              · linarith only [h1416, h2, hlam]
                              · rcases p1402_3 (m.d 1 5) (by simp) with h1418 | h1418
                                · linarith only [h1418, h3, hlam]
                                · rcases h5bigk with h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1289, h1290, h6, hc24, hc45, hlam, hphi, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1289, h1290, h6, hc45, hlam, hphi, ht12, ht23, ht34, p1420_1, u1ehi3]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1424 | h1424
                                    · rcases p1420_3 (m.d 1 5) (by simp) with h1425 | h1425
                                      · linarith only [h1425, h3, hlam]
                                      · linarith only [h1393, h1425, hlam]
                                    · linarith only [h1424, h5, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h6, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h3, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1290, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1393, hc01, hc35, hlam, hphi, ht0b, ht5b, p1402_1, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1394, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1289, h1290, h1397, h3, h4, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1420_1, u1ehi3]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h0, h1289, h1290, h1397, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1420_1, u1ehi3]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1438 | h1438
                                    · rcases p1420_3 (m.d 1 5) (by simp) with h1439 | h1439
                                      · linarith only [h1290, h1439, hlam]
                                      · linarith only [h1393, h1439, hlam]
                                    · linarith only [h1438, h5, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1398, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h5, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1393, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1397, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1400, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1289, h1290, h3, hc45, hlam, hphi, ht12, ht23, ht34, p1420_1, u1ehi3]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1289, h1290, hc45, hlam, hphi, ht12, ht23, ht34, p1420_1, u1ehi3]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1289, h1290, hc45, hlam, hphi, ht12, ht23, ht34, p1420_1, u1ehi3]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1452 | h1452
                                    · linarith only [h1452, h6, hlam]
                                    · linarith only [h1452, h5, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                        · linarith only [h1411, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        rcases p1402_3 (m.d 0 1) (by simp) with h1457 | h1457
                        · rcases p1402_3 (m.d 1 2) (by simp) with h1458 | h1458
                          · linarith only [h0, h1458, hlam]
                          · linarith only [h1289, h1458, hlam]
                        · linarith only [h1457, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        rcases p1402_3 (m.d 0 1) (by simp) with h1462 | h1462
                        · rcases p1402_3 (m.d 1 2) (by simp) with h1463 | h1463
                          · linarith only [h0, h1463, hlam]
                          · rcases p1402_3 (m.d 1 3) (by simp) with h1465 | h1465
                            · linarith only [h1, h1465, hlam]
                            · linarith only [h1393, h1465, hlam]
                        · linarith only [h1462, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h0, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1088, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [hc12, hlam, hphi, p1402_1, u1ehi3]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1290, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h0, h1088, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1402_1, u1ehi1]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h0, h1088, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1402_1, u1ehi3]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h0, h1088, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1402_1, u1ehi4]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h2, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1289, hlam, p1402_1]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1392, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1394, hlam, p1402_1]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h3, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1289, hc15, hlam, hphi, p1402_1, u1ehi3]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h1393, hlam, p1402_0]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [h0, h1088, h1393, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1402_1, u1ehi3]
                      · have p1402_0 := h1402c.1
                        have p1402_1 := h1402c.2.1
                        have p1402_2 := h1402c.2.2.1
                        have p1402_3 := h1402c.2.2.2
                        linarith only [hlam, p1402_0]
                · linarith only [h0, h1088, h1289, h1397, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
              · linarith only [h1088, h1289, h1396, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1491 | h1491
            · linarith only [h1491, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1493 | h1493
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1494 | h1494
                · linarith only [h1393, h1494, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h0, h1088, h1289, h1494, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
              · linarith only [h1088, h1289, h1493, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h1088, h1289, h1392, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1499 | h1499
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1500 | h1500
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1501 | h1501
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1502 | h1502
            · linarith only [h1502, h2, h6, hlam]
            · linarith only [h1289, h1499, h1502, hlam]
          · linarith only [h1289, h1499, h1500, h1501, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1506 | h1506
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1507 | h1507
            · linarith only [h1507, h2, h6, hlam]
            · linarith only [h1088, h1499, h1500, h1507, hlam]
          · linarith only [h1088, h1499, h1506, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1512 | h1512
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1513 | h1513
            · linarith only [h1513, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1515 | h1515
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1516 | h1516
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1517 | h1517
                  · linarith only [h1515, h1517, h2, h6, hc23, hlam, hphi, ht12, u1ehi3]
                  · linarith only [h1289, h1517, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h1088, h1512, h1516, hc13, hlam, hphi, u1ehi1]
              · linarith only [h1088, h1511, h1515, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1522 | h1522
            · linarith only [h0, h1511, h1512, h1522, h4, h5, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1524 | h1524
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1525 | h1525
                · linarith only [h0, h1511, h1512, h1525, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1088, h1525, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1088, h1524, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1529 | h1529
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1530 | h1530
            · linarith only [h1530, h2, h6, hlam]
            · linarith only [h1511, h1529, h1530, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1533 | h1533
            · linarith only [h1533, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1535 | h1535
              · linarith only [h1088, h1511, h1535, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h1088, h1535, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_21_15_M_IR_L_I_s3_x0_x0_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_21_15_M_IR_L_I_s3_x0_x0_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h5 h6

end R2N4
