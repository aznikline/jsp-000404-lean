import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1157 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h1158 | h1158
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1159 | h1159
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1160 | h1160
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1161 | h1161
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1162 | h1162
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1163 | h1163
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1164 | h1164
              · linarith only [h0, h1157, h1164, h3, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1157, h1161, h1164, h3, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1158, h1160, h1163, h8, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h0, h1157, h1161, h1162, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1171 | h1171
              · linarith only [h1157, h1161, h1171, h8, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1173 | h1173
                · linarith only [h1157, h1161, h1169, h1173, hlam]
                · rcases h2bigk with h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c | h1175c
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    rcases p1175_3 (m.d 0 2) (by simp) with h1177 | h1177
                    · rcases p1175_3 (m.d 1 2) (by simp) with h1178 | h1178
                      · linarith only [h0, h1178, hlam]
                      · rcases p1175_3 (m.d 2 3) (by simp) with h1180 | h1180
                        · linarith only [h1180, h3, hlam]
                        · linarith only [h1180, h8, hlam]
                    · linarith only [h0, h1177, hlam]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h0, h1157, h1169, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1157, h3, h8, hlam, p1175_2]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1158, h3, h8, hlam, p1175_2]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h0, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h8, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h0, h3, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h0, h3, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h3, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h0, h1157, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    rcases p1175_3 (m.d 0 2) (by simp) with h1195 | h1195
                    · rcases p1175_3 (m.d 1 2) (by simp) with h1196 | h1196
                      · linarith only [h1196, h8, hlam]
                      · linarith only [h1157, h1196, hlam]
                    · linarith only [h1195, h4, hlam]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    rcases p1175_3 (m.d 0 2) (by simp) with h1200 | h1200
                    · rcases p1175_3 (m.d 1 2) (by simp) with h1201 | h1201
                      · linarith only [h1201, h8, hlam]
                      · linarith only [h1158, h1201, hlam]
                    · linarith only [h1200, h5, hlam]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h4, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1157, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1169, hlam, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1171, hlam, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h5, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1158, hlam, p1175_0]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h1170, hlam, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [h0, h1158, h1169, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1175_1]
                  · have p1175_0 := h1175c.1
                    have p1175_1 := h1175c.2.1
                    have p1175_2 := h1175c.2.2.1
                    have p1175_3 := h1175c.2.2.2
                    linarith only [hlam, p1175_0]
            · linarith only [h1160, h1170, h8, hlam]
          · linarith only [h0, h1158, h1169, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1158, h1160, h8, hlam]
    · linarith only [h1157, h1159, h8, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1219 | h1219
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1220 | h1220
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1221 | h1221
        · linarith only [h1157, h1158, h1221, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1223 | h1223
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1224 | h1224
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1225 | h1225
              · linarith only [h1157, h1158, h1221, h1225, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1227 | h1227
                · linarith only [h1157, h1158, h1223, h1225, h1227, hlam]
                · rcases h2bigk with h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    rcases p1229_3 (m.d 0 2) (by simp) with h1231 | h1231
                    · rcases p1229_3 (m.d 1 2) (by simp) with h1232 | h1232
                      · linarith only [h0, h1232, hlam]
                      · rcases p1229_3 (m.d 2 3) (by simp) with h1234 | h1234
                        · linarith only [h1234, h3, hlam]
                        · linarith only [h1234, h8, hlam]
                    · linarith only [h0, h1231, hlam]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h0, h1157, h1158, h1224, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1157, h1158, h1224, h3, hlam, p1229_2]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h0, h1157, h1158, h1223, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h0, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h8, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1158, h1223, h1225, hc34, hc45, hlam, hphi, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1158, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h3, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h0, h1157, h1223, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    rcases p1229_3 (m.d 0 2) (by simp) with h1249 | h1249
                    · rcases p1229_3 (m.d 1 2) (by simp) with h1250 | h1250
                      · linarith only [h1250, h8, hlam]
                      · linarith only [h1157, h1250, hlam]
                    · linarith only [h1249, h4, hlam]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h0, h1157, h1158, h1223, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h4, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1157, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1223, hlam, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1225, hlam, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h5, hlam, p1229_0]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h0, h1157, h1223, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [h1224, hlam, p1229_1]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    rcases p1229_3 (m.d 0 2) (by simp) with h1263 | h1263
                    · rcases p1229_3 (m.d 1 2) (by simp) with h1264 | h1264
                      · linarith only [h1158, h1264, hlam]
                      · linarith only [h1157, h1264, hlam]
                    · linarith only [h1263, h4, hlam]
                  · have p1229_0 := h1229c.1
                    have p1229_1 := h1229c.2.1
                    have p1229_2 := h1229c.2.2.1
                    have p1229_3 := h1229c.2.2.2
                    linarith only [hlam, p1229_0]
            · linarith only [h1157, h1220, h1223, h1224, h8, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h0, h1157, h1223, h3, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1271 | h1271
        · linarith only [h1157, h1220, h1271, h8, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1273 | h1273
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1274 | h1274
            · linarith only [h0, h1157, h1220, h1273, h1274, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1276 | h1276
              · linarith only [h1157, h1274, h1276, h8, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1278 | h1278
                · linarith only [h1157, h1273, h1274, h1276, h1278, h8, hlam]
                · linarith only [h0, h1157, h1273, h1274, h1278, h3, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1157, h1273, h3, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h1157, h1219, h8, hlam]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1157 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1283 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h1284 | h1284
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1285 | h1285
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1286 | h1286
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1287 | h1287
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1288 | h1288
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1289 | h1289
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1290 | h1290
              · rcases h2bigk with h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  rcases p1291_3 (m.d 0 2) (by simp) with h1293 | h1293
                  · rcases p1291_3 (m.d 1 2) (by simp) with h1294 | h1294
                    · linarith only [h0, h1294, hlam]
                    · rcases p1291_3 (m.d 2 3) (by simp) with h1296 | h1296
                      · linarith only [h1296, h3, hlam]
                      · linarith only [h1296, h8, hlam]
                  · linarith only [h0, h1293, hlam]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h0, h1157, h1283, h1287, h1288, h1290, hc01, hc45, hlam, hphi, ht0b, ht5b, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h0, h1157, h1283, h1288, h1290, hc01, hc45, hlam, hphi, ht0b, ht5b, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1157, h1283, h1287, h3, hlam, p1291_2]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h0, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h8, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1157, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1157, h1287, h1288, h1290, h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h3, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h0, h1283, h1288, h1290, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h0, h1157, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  rcases p1291_3 (m.d 0 2) (by simp) with h1312 | h1312
                  · rcases p1291_3 (m.d 1 2) (by simp) with h1313 | h1313
                    · linarith only [h1313, h8, hlam]
                    · linarith only [h1283, h1313, hlam]
                  · linarith only [h1312, h5, hlam]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h4, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h0, h1283, h1288, h1290, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1287, hlam, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  rcases p1291_3 (m.d 0 2) (by simp) with h1321 | h1321
                  · rcases p1291_3 (m.d 1 2) (by simp) with h1322 | h1322
                    · linarith only [h1157, h1322, hlam]
                    · linarith only [h1283, h1322, hlam]
                  · linarith only [h1321, h5, hlam]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h5, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1283, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1288, hlam, p1291_1]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [h1289, hlam, p1291_0]
                · have p1291_0 := h1291c.1
                  have p1291_1 := h1291c.2.1
                  have p1291_2 := h1291c.2.2.1
                  have p1291_3 := h1291c.2.2.2
                  linarith only [hlam, p1291_0]
              · linarith only [h0, h1283, h1289, h1290, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1157, h1283, h1284, h1286, h1289, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1285, h1288, h8, hlam]
        · linarith only [h0, h1283, h1287, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1157, h1283, h1286, hlam]
    · linarith only [h1283, h1285, h8, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1337 | h1337
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1338 | h1338
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
        · linarith only [h0, h1283, h1284, h1339, h3, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h1283, h1339, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1283, h1284, h1338, h8, hlam]
    · linarith only [h1283, h1337, h8, hlam]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1157 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1283 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1344 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h1345 | h1345
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1346 | h1346
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1347 | h1347
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1348 | h1348
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1349 | h1349
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1350 | h1350
            · rcases h2bigk with h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                rcases p1351_3 (m.d 0 2) (by simp) with h1353 | h1353
                · rcases p1351_3 (m.d 1 2) (by simp) with h1354 | h1354
                  · linarith only [h0, h1354, hlam]
                  · rcases p1351_3 (m.d 2 3) (by simp) with h1356 | h1356
                    · linarith only [h1356, h3, hlam]
                    · linarith only [h1356, h8, hlam]
                · linarith only [h0, h1353, hlam]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h0, h1344, h1350, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p1351_1]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                rcases p1351_3 (m.d 0 2) (by simp) with h1361 | h1361
                · rcases p1351_3 (m.d 1 2) (by simp) with h1362 | h1362
                  · linarith only [h0, h1362, hlam]
                  · rcases p1351_3 (m.d 2 3) (by simp) with h1364 | h1364
                    · linarith only [h1364, h3, hlam]
                    · linarith only [h1347, h1364, hlam]
                · linarith only [h1361, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                rcases p1351_3 (m.d 0 2) (by simp) with h1368 | h1368
                · rcases p1351_3 (m.d 1 2) (by simp) with h1369 | h1369
                  · linarith only [h0, h1369, hlam]
                  · rcases p1351_3 (m.d 2 3) (by simp) with h1371 | h1371
                    · linarith only [h1371, h3, hlam]
                    · linarith only [h1348, h1371, hlam]
                · linarith only [h1368, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h0, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h8, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1157, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1283, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h3, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                rcases p1351_3 (m.d 0 2) (by simp) with h1381 | h1381
                · rcases p1351_3 (m.d 1 2) (by simp) with h1382 | h1382
                  · linarith only [h1382, hlam, p1351_0]
                  · rcases p1351_3 (m.d 2 3) (by simp) with h1384 | h1384
                    · rcases p1351_3 (m.d 2 4) (by simp) with h1385 | h1385
                      · linarith only [h1347, h1385, hlam]
                      · linarith only [h1157, h1385, hlam]
                    · linarith only [h1384, hlam, p1351_0]
                · linarith only [h0, h1381, hlam]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1283, h1349, hc12, hc23, hlam, hphi, p1351_1]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h0, h1283, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1351_1]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h4, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                rcases p1351_3 (m.d 0 2) (by simp) with h1394 | h1394
                · rcases p1351_3 (m.d 1 2) (by simp) with h1395 | h1395
                  · linarith only [h1395, hlam, p1351_0]
                  · rcases p1351_3 (m.d 2 3) (by simp) with h1397 | h1397
                    · rcases p1351_3 (m.d 2 4) (by simp) with h1398 | h1398
                      · rcases p1351_3 (m.d 2 5) (by simp) with h1399 | h1399
                        · linarith only [h1349, h1399, hlam]
                        · linarith only [h1283, h1399, hlam]
                      · linarith only [h1398, hlam, p1351_0]
                    · linarith only [h1397, h8, hlam]
                · linarith only [h0, h1394, hlam]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1347, hlam, p1351_1]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1283, hc12, hc24, hlam, hphi, p1351_1]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h5, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                rcases p1351_3 (m.d 0 2) (by simp) with h1409 | h1409
                · rcases p1351_3 (m.d 1 2) (by simp) with h1410 | h1410
                  · linarith only [h1410, hlam, p1351_0]
                  · rcases p1351_3 (m.d 2 3) (by simp) with h1412 | h1412
                    · rcases p1351_3 (m.d 2 4) (by simp) with h1413 | h1413
                      · rcases p1351_3 (m.d 2 5) (by simp) with h1414 | h1414
                        · rcases h4bigk with h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            rcases p1415_3 (m.d 0 4) (by simp) with h1417 | h1417
                            · rcases p1415_3 (m.d 1 4) (by simp) with h1418 | h1418
                              · linarith only [h1418, h2, hlam]
                              · rcases p1415_3 (m.d 2 4) (by simp) with h1420 | h1420
                                · linarith only [h1420, h4, hlam]
                                · linarith only [h1157, h1420, hlam]
                            · linarith only [h1417, h2, hlam]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h0, h1349, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1351_1, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            rcases p1415_3 (m.d 0 4) (by simp) with h1425 | h1425
                            · rcases p1415_3 (m.d 1 4) (by simp) with h1426 | h1426
                              · linarith only [h1426, h2, hlam]
                              · linarith only [h1344, h1426, hlam]
                            · linarith only [h1425, h6, hlam]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            rcases p1415_3 (m.d 0 4) (by simp) with h1430 | h1430
                            · rcases p1415_3 (m.d 1 4) (by simp) with h1431 | h1431
                              · linarith only [h1431, h2, hlam]
                              · linarith only [h1346, h1431, hlam]
                            · linarith only [h1430, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h2, hlam, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1157, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1350, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            rcases p1415_3 (m.d 0 4) (by simp) with h1439 | h1439
                            · rcases p1415_3 (m.d 1 4) (by simp) with h1440 | h1440
                              · rcases p1415_3 (m.d 2 4) (by simp) with h1441 | h1441
                                · rcases p1415_3 (m.d 3 4) (by simp) with h1442 | h1442
                                  · linarith only [h1344, h1442, hlam]
                                  · linarith only [h1350, h1442, hlam]
                                · linarith only [h1349, h1441, hlam]
                              · linarith only [h1440, hlam, p1415_0]
                            · linarith only [h1439, h7, hlam]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h4, hlam, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h0, h1344, h1350, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h0, h1347, h1350, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            rcases p1415_3 (m.d 0 4) (by simp) with h1452 | h1452
                            · rcases p1415_3 (m.d 1 4) (by simp) with h1453 | h1453
                              · linarith only [h1157, h1453, hlam]
                              · linarith only [h1346, h1453, hlam]
                            · linarith only [h1452, h7, hlam]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h6, hlam, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1344, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1347, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1, h1344, hc01, hc45, hlam, hphi, ht0b, ht5b, p1415_1]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h7, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1346, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1349, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [h1350, hlam, p1415_0]
                          · have p1415_0 := h1415c.1
                            have p1415_1 := h1415c.2.1
                            have p1415_2 := h1415c.2.2.1
                            have p1415_3 := h1415c.2.2.2
                            linarith only [hlam, p1415_0]
                        · linarith only [h1414, hlam, p1351_0]
                      · linarith only [h1157, h1413, hlam]
                    · linarith only [h1412, h8, hlam]
                · linarith only [h0, h1409, hlam]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1348, hlam, p1351_1]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [h1349, hlam, p1351_0]
              · have p1351_0 := h1351c.1
                have p1351_1 := h1351c.2.1
                have p1351_2 := h1351c.2.2.1
                have p1351_3 := h1351c.2.2.2
                linarith only [hlam, p1351_0]
            · rcases h2bigk with h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                rcases p1474_3 (m.d 0 2) (by simp) with h1476 | h1476
                · rcases p1474_3 (m.d 1 2) (by simp) with h1477 | h1477
                  · linarith only [h0, h1477, hlam]
                  · rcases p1474_3 (m.d 2 3) (by simp) with h1479 | h1479
                    · linarith only [h1479, h3, hlam]
                    · linarith only [h1479, h8, hlam]
                · linarith only [h0, h1476, hlam]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h0, h1157, h1346, h1347, h1350, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h0, h1157, h1346, h1350, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                rcases p1474_3 (m.d 0 2) (by simp) with h1485 | h1485
                · rcases p1474_3 (m.d 1 2) (by simp) with h1486 | h1486
                  · linarith only [h0, h1486, hlam]
                  · rcases p1474_3 (m.d 2 3) (by simp) with h1488 | h1488
                    · linarith only [h1488, h3, hlam]
                    · linarith only [h1348, h1488, hlam]
                · linarith only [h1485, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h0, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h8, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1157, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1283, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h3, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                rcases p1474_3 (m.d 0 2) (by simp) with h1498 | h1498
                · rcases p1474_3 (m.d 1 2) (by simp) with h1499 | h1499
                  · linarith only [h1499, hlam, p1474_0]
                  · rcases p1474_3 (m.d 2 3) (by simp) with h1501 | h1501
                    · rcases p1474_3 (m.d 2 4) (by simp) with h1502 | h1502
                      · linarith only [h1347, h1502, hlam]
                      · linarith only [h1157, h1502, hlam]
                    · linarith only [h1501, hlam, p1474_0]
                · linarith only [h0, h1498, hlam]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1157, h1346, h1350, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h0, h1283, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h4, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                rcases p1474_3 (m.d 0 2) (by simp) with h1511 | h1511
                · rcases p1474_3 (m.d 1 2) (by simp) with h1512 | h1512
                  · linarith only [h1512, hlam, p1474_0]
                  · rcases p1474_3 (m.d 2 3) (by simp) with h1514 | h1514
                    · rcases p1474_3 (m.d 2 4) (by simp) with h1515 | h1515
                      · rcases p1474_3 (m.d 2 5) (by simp) with h1516 | h1516
                        · linarith only [h1349, h1516, hlam]
                        · linarith only [h1283, h1516, hlam]
                      · linarith only [h1515, hlam, p1474_0]
                    · linarith only [h1514, h8, hlam]
                · linarith only [h0, h1511, hlam]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1347, hlam, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1283, hc12, hc24, hlam, hphi, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h5, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                rcases p1474_3 (m.d 0 2) (by simp) with h1526 | h1526
                · rcases p1474_3 (m.d 1 2) (by simp) with h1527 | h1527
                  · linarith only [h1527, hlam, p1474_0]
                  · rcases p1474_3 (m.d 2 3) (by simp) with h1529 | h1529
                    · rcases p1474_3 (m.d 2 4) (by simp) with h1530 | h1530
                      · rcases p1474_3 (m.d 2 5) (by simp) with h1531 | h1531
                        · rcases h4bigk with h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h0, h1346, h1350, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h0, h1157, h1346, h1350, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            rcases p1532_3 (m.d 0 4) (by simp) with h1536 | h1536
                            · rcases p1532_3 (m.d 1 4) (by simp) with h1537 | h1537
                              · linarith only [h1537, h2, hlam]
                              · linarith only [h1344, h1537, hlam]
                            · linarith only [h1536, h6, hlam]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            rcases p1532_3 (m.d 0 4) (by simp) with h1541 | h1541
                            · rcases p1532_3 (m.d 1 4) (by simp) with h1542 | h1542
                              · linarith only [h1542, h2, hlam]
                              · linarith only [h1346, h1542, hlam]
                            · linarith only [h1541, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h2, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1157, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            rcases p1532_3 (m.d 0 4) (by simp) with h1549 | h1549
                            · rcases p1532_3 (m.d 1 4) (by simp) with h1550 | h1550
                              · rcases p1532_3 (m.d 2 4) (by simp) with h1551 | h1551
                                · rcases p1532_3 (m.d 3 4) (by simp) with h1552 | h1552
                                  · linarith only [h1344, h1552, hlam]
                                  · rcases p1532_3 (m.d 4 5) (by simp) with h1554 | h1554
                                    · linarith only [h1346, h1554, hlam]
                                    · linarith only [h1350, h1554, hlam]
                                · linarith only [h1347, h1551, hlam]
                              · linarith only [h1344, h1550, hlam]
                            · linarith only [h1549, h6, hlam]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1350, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h4, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1346, h1350, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            rcases p1532_3 (m.d 0 4) (by simp) with h1564 | h1564
                            · rcases p1532_3 (m.d 1 4) (by simp) with h1565 | h1565
                              · linarith only [h1157, h1565, hlam]
                              · linarith only [h1344, h1565, hlam]
                            · linarith only [h1564, h6, hlam]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h0, h1347, h1350, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h6, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1344, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1347, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1350, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h7, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1346, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1349, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1346, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                        · linarith only [h1531, hlam, p1474_0]
                      · linarith only [h1157, h1530, hlam]
                    · linarith only [h1529, h8, hlam]
                · linarith only [h0, h1526, hlam]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1348, hlam, p1474_1]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [h1349, hlam, p1474_0]
              · have p1474_0 := h1474c.1
                have p1474_1 := h1474c.2.1
                have p1474_2 := h1474c.2.2.1
                have p1474_3 := h1474c.2.2.2
                linarith only [hlam, p1474_0]
          · linarith only [h1157, h1346, h1349, hlam]
        · linarith only [h1345, h1348, h8, hlam]
      · linarith only [h1344, h1347, h8, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1593 | h1593
            · linarith only [h1344, h1346, h1593, hlam]
            · rcases h2bigk with h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1157, h1346, h1590, h1592, h3, hlam, p1595_2]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1157, h1346, h1590, h1592, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h0, h1157, h1346, h1592, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                rcases p1595_3 (m.d 0 2) (by simp) with h1600 | h1600
                · rcases p1595_3 (m.d 1 2) (by simp) with h1601 | h1601
                  · linarith only [h0, h1601, hlam]
                  · rcases p1595_3 (m.d 2 3) (by simp) with h1603 | h1603
                    · linarith only [h1603, h3, hlam]
                    · linarith only [h1591, h1603, hlam]
                · linarith only [h1600, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h0, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h8, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1157, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1283, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h3, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                rcases p1595_3 (m.d 0 2) (by simp) with h1613 | h1613
                · rcases p1595_3 (m.d 1 2) (by simp) with h1614 | h1614
                  · linarith only [h1614, hlam, p1595_0]
                  · rcases p1595_3 (m.d 2 3) (by simp) with h1616 | h1616
                    · rcases p1595_3 (m.d 2 4) (by simp) with h1617 | h1617
                      · linarith only [h1590, h1617, hlam]
                      · linarith only [h1157, h1617, hlam]
                    · linarith only [h1616, hlam, p1595_0]
                · linarith only [h0, h1613, hlam]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1157, h1346, h1592, hc12, hc23, hlam, hphi, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h0, h1283, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h4, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                rcases p1595_3 (m.d 0 2) (by simp) with h1626 | h1626
                · rcases p1595_3 (m.d 1 2) (by simp) with h1627 | h1627
                  · linarith only [h1627, hlam, p1595_0]
                  · rcases p1595_3 (m.d 2 3) (by simp) with h1629 | h1629
                    · rcases p1595_3 (m.d 2 4) (by simp) with h1630 | h1630
                      · rcases p1595_3 (m.d 2 5) (by simp) with h1631 | h1631
                        · linarith only [h1592, h1631, hlam]
                        · linarith only [h1283, h1631, hlam]
                      · linarith only [h1630, hlam, p1595_0]
                    · linarith only [h1629, h8, hlam]
                · linarith only [h0, h1626, hlam]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1590, hlam, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1157, h1346, h1592, hc12, hc24, hlam, hphi, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h5, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                rcases p1595_3 (m.d 0 2) (by simp) with h1641 | h1641
                · rcases p1595_3 (m.d 1 2) (by simp) with h1642 | h1642
                  · linarith only [h1642, hlam, p1595_0]
                  · rcases p1595_3 (m.d 2 3) (by simp) with h1644 | h1644
                    · rcases p1595_3 (m.d 2 4) (by simp) with h1645 | h1645
                      · rcases p1595_3 (m.d 2 5) (by simp) with h1646 | h1646
                        · rcases h4bigk with h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            rcases p1647_3 (m.d 0 4) (by simp) with h1649 | h1649
                            · rcases p1647_3 (m.d 1 4) (by simp) with h1650 | h1650
                              · linarith only [h1650, h2, hlam]
                              · rcases p1647_3 (m.d 2 4) (by simp) with h1652 | h1652
                                · linarith only [h1652, h4, hlam]
                                · linarith only [h1157, h1652, hlam]
                            · linarith only [h1649, h2, hlam]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1157, h1346, h1592, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            rcases p1647_3 (m.d 0 4) (by simp) with h1657 | h1657
                            · rcases p1647_3 (m.d 1 4) (by simp) with h1658 | h1658
                              · linarith only [h1658, h2, hlam]
                              · linarith only [h1344, h1658, hlam]
                            · linarith only [h1657, h6, hlam]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            rcases p1647_3 (m.d 0 4) (by simp) with h1662 | h1662
                            · rcases p1647_3 (m.d 1 4) (by simp) with h1663 | h1663
                              · linarith only [h1663, h2, hlam]
                              · rcases p1647_3 (m.d 2 4) (by simp) with h1665 | h1665
                                · linarith only [h1665, h4, hlam]
                                · linarith only [h1592, h1665, hlam]
                            · linarith only [h1662, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h2, hlam, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1157, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1346, h1592, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1346, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h4, hlam, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            rcases p1647_3 (m.d 0 4) (by simp) with h1675 | h1675
                            · rcases p1647_3 (m.d 1 4) (by simp) with h1676 | h1676
                              · linarith only [h1157, h1676, hlam]
                              · rcases p1647_3 (m.d 2 4) (by simp) with h1678 | h1678
                                · rcases p1647_3 (m.d 3 4) (by simp) with h1679 | h1679
                                  · linarith only [h1590, h1679, hlam]
                                  · rcases p1647_3 (m.d 4 5) (by simp) with h1681 | h1681
                                    · linarith only [h1592, h1681, hlam]
                                    · linarith only [h1346, h1681, hlam]
                                · linarith only [h1157, h1678, hlam]
                            · linarith only [h1675, h2, hlam]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            rcases p1647_3 (m.d 0 4) (by simp) with h1687 | h1687
                            · rcases p1647_3 (m.d 1 4) (by simp) with h1688 | h1688
                              · linarith only [h1157, h1688, hlam]
                              · linarith only [h1344, h1688, hlam]
                            · linarith only [h1687, h6, hlam]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h0, h1157, h1346, h1590, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h6, hlam, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1344, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1590, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1593, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h7, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h0, h1157, h1590, h1592, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h1592, hlam, p1647_0]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [h0, h1590, h1592, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1647_1]
                          · have p1647_0 := h1647c.1
                            have p1647_1 := h1647c.2.1
                            have p1647_2 := h1647c.2.2.1
                            have p1647_3 := h1647c.2.2.2
                            linarith only [hlam, p1647_0]
                        · linarith only [h1646, hlam, p1595_0]
                      · linarith only [h1157, h1645, hlam]
                    · linarith only [h1644, h8, hlam]
                · linarith only [h0, h1641, hlam]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1591, hlam, p1595_1]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [h1592, hlam, p1595_0]
              · have p1595_0 := h1595c.1
                have p1595_1 := h1595c.2.1
                have p1595_2 := h1595c.2.2.1
                have p1595_3 := h1595c.2.2.2
                linarith only [hlam, p1595_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1710 | h1710
            · linarith only [h0, h1157, h1592, h1710, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1157, h1592, h3, h6, h7, hlam, p1712_2]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                rcases p1712_3 (m.d 0 2) (by simp) with h1715 | h1715
                · rcases p1712_3 (m.d 1 2) (by simp) with h1716 | h1716
                  · linarith only [h0, h1716, hlam]
                  · rcases p1712_3 (m.d 2 3) (by simp) with h1718 | h1718
                    · linarith only [h1718, hlam, p1712_0]
                    · rcases p1712_3 (m.d 2 4) (by simp) with h1720 | h1720
                      · linarith only [h1720, h4, hlam]
                      · rcases p1712_3 (m.d 2 5) (by simp) with h1722 | h1722
                        · linarith only [h1722, h5, hlam]
                        · rcases h4bigk with h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            rcases p1724_3 (m.d 0 4) (by simp) with h1726 | h1726
                            · rcases p1724_3 (m.d 1 4) (by simp) with h1727 | h1727
                              · linarith only [h1727, h2, hlam]
                              · rcases p1724_3 (m.d 2 4) (by simp) with h1729 | h1729
                                · linarith only [h1729, h4, hlam]
                                · linarith only [h1157, h1729, hlam]
                            · linarith only [h1726, h2, hlam]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            rcases p1724_3 (m.d 0 4) (by simp) with h1733 | h1733
                            · rcases p1724_3 (m.d 1 4) (by simp) with h1734 | h1734
                              · linarith only [h1734, h2, hlam]
                              · rcases p1724_3 (m.d 2 4) (by simp) with h1736 | h1736
                                · linarith only [h1736, h4, hlam]
                                · rcases p1724_3 (m.d 3 4) (by simp) with h1738 | h1738
                                  · linarith only [h1738, h6, hlam]
                                  · rcases p1724_3 (m.d 4 5) (by simp) with h1740 | h1740
                                    · linarith only [h1740, h7, hlam]
                                    · linarith only [h1592, h1740, hlam]
                            · linarith only [h1733, h4, hlam]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            rcases p1724_3 (m.d 0 4) (by simp) with h1744 | h1744
                            · rcases p1724_3 (m.d 1 4) (by simp) with h1745 | h1745
                              · linarith only [h1745, h2, hlam]
                              · linarith only [h1344, h1745, hlam]
                            · linarith only [h1744, h6, hlam]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1157, h1592, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h2, hlam, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1157, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1157, h1592, hc34, hc45, hlam, hphi, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1346, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h4, hlam, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1592, hc14, hc45, hlam, hphi, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h0, h1592, h3, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1592, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h6, hlam, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1344, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1590, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h1710, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h7, hlam, p1724_0]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            rcases p1724_3 (m.d 0 4) (by simp) with h1766 | h1766
                            · rcases p1724_3 (m.d 1 4) (by simp) with h1767 | h1767
                              · linarith only [h1767, hlam, p1724_0]
                              · rcases p1724_3 (m.d 2 4) (by simp) with h1769 | h1769
                                · linarith only [h1592, h1769, hlam]
                                · linarith only [h1157, h1769, hlam]
                            · linarith only [h1766, h2, hlam]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [h0, h1157, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1724_1]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            rcases p1724_3 (m.d 0 4) (by simp) with h1774 | h1774
                            · rcases p1724_3 (m.d 1 4) (by simp) with h1775 | h1775
                              · linarith only [h1346, h1775, hlam]
                              · linarith only [h1344, h1775, hlam]
                            · linarith only [h1774, h6, hlam]
                          · have p1724_0 := h1724c.1
                            have p1724_1 := h1724c.2.1
                            have p1724_2 := h1724c.2.2.1
                            have p1724_3 := h1724c.2.2.2
                            linarith only [hlam, p1724_0]
                · linarith only [h1715, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                rcases p1712_3 (m.d 0 2) (by simp) with h1781 | h1781
                · rcases p1712_3 (m.d 1 2) (by simp) with h1782 | h1782
                  · linarith only [h0, h1782, hlam]
                  · rcases p1712_3 (m.d 2 3) (by simp) with h1784 | h1784
                    · linarith only [h1784, h3, hlam]
                    · linarith only [h1590, h1784, hlam]
                · linarith only [h1781, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                rcases p1712_3 (m.d 0 2) (by simp) with h1788 | h1788
                · rcases p1712_3 (m.d 1 2) (by simp) with h1789 | h1789
                  · linarith only [h0, h1789, hlam]
                  · rcases p1712_3 (m.d 2 3) (by simp) with h1791 | h1791
                    · linarith only [h1791, h3, hlam]
                    · linarith only [h1591, h1791, hlam]
                · linarith only [h1788, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h0, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h8, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1157, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1283, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h3, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                rcases p1712_3 (m.d 0 2) (by simp) with h1801 | h1801
                · rcases p1712_3 (m.d 1 2) (by simp) with h1802 | h1802
                  · linarith only [h1802, hlam, p1712_0]
                  · rcases p1712_3 (m.d 2 3) (by simp) with h1804 | h1804
                    · rcases p1712_3 (m.d 2 4) (by simp) with h1805 | h1805
                      · linarith only [h1590, h1805, hlam]
                      · linarith only [h1157, h1805, hlam]
                    · linarith only [h1804, hlam, p1712_0]
                · linarith only [h0, h1801, hlam]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1157, hc12, hc23, hlam, hphi, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h0, h1283, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h4, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h0, h1592, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1590, hlam, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1592, hlam, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h5, hlam, p1712_0]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                rcases p1712_3 (m.d 0 2) (by simp) with h1819 | h1819
                · rcases p1712_3 (m.d 1 2) (by simp) with h1820 | h1820
                  · linarith only [h1820, hlam, p1712_0]
                  · rcases p1712_3 (m.d 2 3) (by simp) with h1822 | h1822
                    · rcases p1712_3 (m.d 2 4) (by simp) with h1823 | h1823
                      · linarith only [h1592, h1823, hlam]
                      · linarith only [h1157, h1823, hlam]
                    · linarith only [h1822, h8, hlam]
                · linarith only [h0, h1819, hlam]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1591, hlam, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [h1157, hc12, hc25, hlam, hphi, p1712_1]
              · have p1712_0 := h1712c.1
                have p1712_1 := h1712c.2.1
                have p1712_2 := h1712c.2.2.1
                have p1712_3 := h1712c.2.2.2
                linarith only [hlam, p1712_0]
        · linarith only [h1345, h1591, h8, hlam]
      · linarith only [h1344, h1590, h8, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1833 | h1833
    · linarith only [h1344, h1345, h1833, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1835 | h1835
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1836 | h1836
        · linarith only [h0, h1344, h1345, h1836, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1838 | h1838
          · linarith only [h1157, h1833, h1835, h1836, h1838, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1840 | h1840
            · linarith only [h1, h1344, h1838, h1840, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h2bigk with h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h1836, h1840, h3, h6, h7, h8, hlam, p1842_2]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                rcases p1842_3 (m.d 0 2) (by simp) with h1845 | h1845
                · rcases p1842_3 (m.d 1 2) (by simp) with h1846 | h1846
                  · linarith only [h0, h1846, hlam]
                  · rcases p1842_3 (m.d 2 3) (by simp) with h1848 | h1848
                    · linarith only [h1848, hlam, p1842_0]
                    · rcases p1842_3 (m.d 2 4) (by simp) with h1850 | h1850
                      · linarith only [h1850, h4, hlam]
                      · rcases p1842_3 (m.d 2 5) (by simp) with h1852 | h1852
                        · linarith only [h1852, h5, hlam]
                        · linarith only [h1836, h1852, hlam]
                · linarith only [h1845, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                rcases p1842_3 (m.d 0 2) (by simp) with h1856 | h1856
                · rcases p1842_3 (m.d 1 2) (by simp) with h1857 | h1857
                  · linarith only [h0, h1857, hlam]
                  · rcases p1842_3 (m.d 2 3) (by simp) with h1859 | h1859
                    · linarith only [h1859, h3, hlam]
                    · linarith only [h1835, h1859, hlam]
                · linarith only [h1856, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                rcases p1842_3 (m.d 0 2) (by simp) with h1863 | h1863
                · rcases p1842_3 (m.d 1 2) (by simp) with h1864 | h1864
                  · linarith only [h0, h1864, hlam]
                  · rcases p1842_3 (m.d 2 3) (by simp) with h1866 | h1866
                    · linarith only [h1866, h3, hlam]
                    · rcases p1842_3 (m.d 2 4) (by simp) with h1868 | h1868
                      · linarith only [h1868, h4, hlam]
                      · rcases p1842_3 (m.d 2 5) (by simp) with h1870 | h1870
                        · linarith only [h1870, hlam, p1842_0]
                        · rcases h4bigk with h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            rcases p1872_3 (m.d 0 4) (by simp) with h1874 | h1874
                            · rcases p1872_3 (m.d 1 4) (by simp) with h1875 | h1875
                              · linarith only [h1875, h2, hlam]
                              · rcases p1872_3 (m.d 2 4) (by simp) with h1877 | h1877
                                · linarith only [h1877, h4, hlam]
                                · linarith only [h1157, h1877, hlam]
                            · linarith only [h1874, h2, hlam]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            rcases p1872_3 (m.d 0 4) (by simp) with h1881 | h1881
                            · rcases p1872_3 (m.d 1 4) (by simp) with h1882 | h1882
                              · linarith only [h1882, h2, hlam]
                              · rcases p1872_3 (m.d 2 4) (by simp) with h1884 | h1884
                                · linarith only [h1884, h4, hlam]
                                · rcases p1872_3 (m.d 3 4) (by simp) with h1886 | h1886
                                  · linarith only [h1886, h6, hlam]
                                  · rcases p1872_3 (m.d 4 5) (by simp) with h1888 | h1888
                                    · linarith only [h1888, h7, hlam]
                                    · linarith only [h1838, h1888, hlam]
                            · linarith only [h1881, h4, hlam]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1344, h1836, h1840, h7, h8, hlam, p1872_2]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h0, h1157, h1835, h1836, h1840, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h2, hlam, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1157, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1157, h1835, h1836, h1840, hc34, hc45, hlam, hphi, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1833, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h4, hlam, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1835, h1836, h1840, hc14, hc45, hlam, hphi, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h0, h1835, h1836, h1840, h3, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1838, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h6, hlam, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1344, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1835, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h1840, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h7, hlam, p1872_0]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            rcases p1872_3 (m.d 0 4) (by simp) with h1910 | h1910
                            · rcases p1872_3 (m.d 1 4) (by simp) with h1911 | h1911
                              · linarith only [h1911, hlam, p1872_0]
                              · rcases p1872_3 (m.d 2 4) (by simp) with h1913 | h1913
                                · linarith only [h1838, h1913, hlam]
                                · linarith only [h1157, h1913, hlam]
                            · linarith only [h1910, h2, hlam]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [h0, h1157, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1872_1]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            rcases p1872_3 (m.d 0 4) (by simp) with h1918 | h1918
                            · rcases p1872_3 (m.d 1 4) (by simp) with h1919 | h1919
                              · linarith only [h1833, h1919, hlam]
                              · linarith only [h1344, h1919, hlam]
                            · linarith only [h1918, h6, hlam]
                          · have p1872_0 := h1872c.1
                            have p1872_1 := h1872c.2.1
                            have p1872_2 := h1872c.2.2.1
                            have p1872_3 := h1872c.2.2.2
                            linarith only [hlam, p1872_0]
                · linarith only [h1863, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h0, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h8, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h1157, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h1283, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h3, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h0, h1836, h1840, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h0, h1157, h1836, h1840, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h1836, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h4, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h0, h1835, h1836, h1840, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h1835, hlam, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h1838, hlam, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h5, hlam, p1842_0]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                rcases p1842_3 (m.d 0 2) (by simp) with h1941 | h1941
                · rcases p1842_3 (m.d 1 2) (by simp) with h1942 | h1942
                  · linarith only [h1942, hlam, p1842_0]
                  · rcases p1842_3 (m.d 2 3) (by simp) with h1944 | h1944
                    · linarith only [h1836, h1944, hlam]
                    · linarith only [h1944, h8, hlam]
                · linarith only [h0, h1941, hlam]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h0, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [h0, h1157, h1836, h1840, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1842_1]
              · have p1842_0 := h1842c.1
                have p1842_1 := h1842c.2.1
                have p1842_2 := h1842c.2.2.1
                have p1842_3 := h1842c.2.2.2
                linarith only [hlam, p1842_0]
      · linarith only [h1344, h1835, h8, hlam]

end R2N4
