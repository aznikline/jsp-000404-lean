import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S7
import Jsp000404.R1LeavesN7_28S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1145 | h1145
  · linarith only [h1145, h3, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1147 | h1147
    · linarith only [h1147, h3, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1149 | h1149
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1150 | h1150
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1151 | h1151
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1152 | h1152
            · linarith only [h0, h1152, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1154 | h1154
              · linarith only [h0, h1145, h1154, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1156 | h1156
                · linarith only [h0, h1147, h1156, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1158 | h1158
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1159 | h1159
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1160 | h1160
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1161 | h1161
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1162 | h1162
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1163 | h1163
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1164 | h1164
                              · rcases h0bigk with h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1167 | h1167
                                  · rcases p1165_3 (m.d 0 2) (by simp) with h1168 | h1168
                                    · linarith only [h0, h1168, hlam]
                                    · rcases p1165_3 (m.d 0 3) (by simp) with h1170 | h1170
                                      · linarith only [h1, h1170, hlam]
                                      · linarith only [h1170, h3, hlam]
                                  · linarith only [h0, h1167, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1, h1158, h1164, hc01, hc45, hlam, hphi, ht0b, ht5b, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1175 | h1175
                                  · rcases p1165_3 (m.d 0 2) (by simp) with h1176 | h1176
                                    · linarith only [h0, h1176, hlam]
                                    · rcases p1165_3 (m.d 0 3) (by simp) with h1178 | h1178
                                      · linarith only [h1, h1178, hlam]
                                      · linarith only [h1149, h1178, hlam]
                                  · linarith only [h1175, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1182 | h1182
                                  · rcases p1165_3 (m.d 0 2) (by simp) with h1183 | h1183
                                    · linarith only [h0, h1183, hlam]
                                    · rcases p1165_3 (m.d 0 3) (by simp) with h1185 | h1185
                                      · linarith only [h1, h1185, hlam]
                                      · linarith only [h1150, h1185, hlam]
                                  · linarith only [h1182, h2, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h3, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1145, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1147, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, h3, hc23, hlam, hphi, p1165_1, u2ehi1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, h1145, h3, hc23, hlam, hphi, p1165_1, u2ehi1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, h1147, h3, hc23, hlam, hphi, p1165_1, u2ehi1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1, h1158, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, h1145, hc24, hlam, hphi, p1165_1, u2ehi1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1149, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, h1147, h1149, h3, hc23, hlam, hphi, p1165_1, u2ehi1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h2, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, h1147, hc25, hlam, hphi, p1165_1, u2ehi1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1150, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1151, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                              · rcases h0bigk with h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  rcases p1209_3 (m.d 0 1) (by simp) with h1211 | h1211
                                  · rcases p1209_3 (m.d 0 2) (by simp) with h1212 | h1212
                                    · linarith only [h0, h1212, hlam]
                                    · rcases p1209_3 (m.d 0 3) (by simp) with h1214 | h1214
                                      · linarith only [h1, h1214, hlam]
                                      · linarith only [h1214, h3, hlam]
                                  · linarith only [h0, h1211, hlam]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1, h1158, h1160, h1164, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1209_1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1151, h1164, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1209_1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  rcases p1209_3 (m.d 0 1) (by simp) with h1220 | h1220
                                  · rcases p1209_3 (m.d 0 2) (by simp) with h1221 | h1221
                                    · linarith only [h0, h1221, hlam]
                                    · rcases p1209_3 (m.d 0 3) (by simp) with h1223 | h1223
                                      · linarith only [h1, h1223, hlam]
                                      · linarith only [h1150, h1223, hlam]
                                  · linarith only [h1220, h2, hlam]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h3, hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1145, hlam, p1209_1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1147, hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1, hlam, p1209_1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, h3, hc23, hlam, hphi, p1209_1, u2ehi1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1151, h1164, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1209_1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, h1147, h3, hc23, hlam, hphi, p1209_1, u2ehi1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1209_1, u2ehi1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, h1145, h1161, hc23, hlam, hphi, p1209_1, u2ehi1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1149, hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, h1145, h1147, h1161, hc23, hlam, hphi, p1209_1, u2ehi1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h2, hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h0, h1147, h1161, h1163, hc23, hlam, hphi, p1209_1, u2ehi1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1150, hlam, p1209_0]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [h1151, hlam, p1209_1]
                                · have p1209_0 := h1209c.1
                                  have p1209_1 := h1209c.2.1
                                  have p1209_2 := h1209c.2.2.1
                                  have p1209_3 := h1209c.2.2.2
                                  linarith only [hlam, p1209_0]
                            · linarith only [h1, h1158, h1160, h1163, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h0, h1162, h3, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h0, h1161, h3, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h1149, h1151, h1154, h1160, h3, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h1150, h1154, h1158, h1159, h3, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h1149, h1152, h1158, h3, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1253 | h1253
            · linarith only [h0, h1145, h1253, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1255 | h1255
              · linarith only [h0, h1255, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1257 | h1257
                · linarith only [h0, h1145, h1151, h1257, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1259 | h1259
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1260 | h1260
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1261 | h1261
                      · linarith only [h1145, h1151, h1255, h1261, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1263 | h1263
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1264 | h1264
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1265 | h1265
                            · linarith only [h0, h1145, h1151, h1263, h1265, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h1145, h1265, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                          · linarith only [h0, h1264, h3, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h0, h1263, h3, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h1150, h1253, h1260, h3, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h1149, h1253, h1259, h3, hc23, hlam, hphi, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1272 | h1272
          · linarith only [h1149, h1150, h1272, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
            · linarith only [h0, h1145, h1274, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1276 | h1276
              · linarith only [h0, h1145, h1276, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1278 | h1278
                · linarith only [h0, h1145, h1272, h1278, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1280 | h1280
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1281 | h1281
                    · linarith only [h1, h1150, h1281, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1283 | h1283
                      · linarith only [h1145, h1272, h1276, h1283, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1285 | h1285
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1286 | h1286
                          · linarith only [h0, h1145, h1149, h1150, h1286, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h1286, h3, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h0, h1, h1280, h1285, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · linarith only [h1149, h1150, h1280, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1291 | h1291
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1292 | h1292
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1293 | h1293
            · linarith only [h0, h1145, h1293, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1295 | h1295
              · linarith only [h0, h1295, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1297 | h1297
                · linarith only [h0, h1147, h1149, h1291, h1297, hc34, hlam, hphi, ht23, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1299 | h1299
                  · linarith only [h1, h1147, h1149, h1291, h1299, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1301 | h1301
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1302 | h1302
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1303 | h1303
                        · linarith only [h0, h1147, h1149, h1291, h1303, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h1303, h3, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h1149, h1291, h1292, h1293, h1299, h1302, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h1149, h1291, h1293, h1301, hc34, hlam, hphi, ht23, u2ehi1]
          · linarith only [h1149, h1291, h1292, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1309 | h1309
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1310 | h1310
            · linarith only [h0, h1310, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1312 | h1312
              · linarith only [h0, h1312, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1314 | h1314
                · linarith only [h0, h1147, h1314, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1316 | h1316
                  · linarith only [h1, h1149, h1316, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1318 | h1318
                    · linarith only [h1, h1291, h1318, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1320 | h1320
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
                        · linarith only [h0, h1149, h1321, h3, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h1321, h3, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h1149, h1309, h1312, h1320, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1325 | h1325
            · linarith only [h0, h1325, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1327 | h1327
              · linarith only [h0, h1327, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1329 | h1329
                · linarith only [h0, h1149, h1309, h1329, h3, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1331 | h1331
                  · linarith only [h1, h1149, h1331, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1333 | h1333
                    · linarith only [h1, h1291, h1333, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1335 | h1335
                      · linarith only [h1149, h1309, h1327, h1335, h3, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1337 | h1337
                        · linarith only [h1149, h1337, h3, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h0, h1337, h3, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1340 | h1340
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1341 | h1341
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1342 | h1342
      · linarith only [h0, h1342, h2, hlam]
      · linarith only [h1341, h1342, hc25, hlam, hphi, u2ehi3]
    · linarith only [h1340, h1341, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1346 | h1346
    · linarith only [h1340, h1346, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1348 | h1348
      · linarith only [h1340, h1348, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1350 | h1350
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1351 | h1351
          · linarith only [h1, h1351, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1353 | h1353
            · linarith only [h0, h1350, h1351, h1353, h2, hc35, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1355 | h1355
              · linarith only [h0, h1346, h1350, h1351, h1355, hc35, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1357 | h1357
                · linarith only [h1, h1346, h1355, h1357, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1359 | h1359
                  · linarith only [h0, h1340, h1359, hc23, hlam, hphi, u2ehi4]
                  · linarith only [h1, h1355, h1359, h2, hc25, hlam, hphi, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1362 | h1362
          · linarith only [h0, h1350, h1362, h2, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1364 | h1364
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
              · linarith only [h0, h1365, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1367 | h1367
                · linarith only [h0, h1340, h1367, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1369 | h1369
                  · linarith only [h1, h1365, h1369, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h1, h1365, h1369, h2, hc25, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
              · linarith only [h0, h1340, h1372, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
                · linarith only [h0, h1346, h1374, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1376 | h1376
                  · linarith only [h1, h1372, h1376, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h1, h1372, h1376, h2, hc25, hlam, hphi, u2ehi1]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1379 | h1379
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1380 | h1380
    · linarith only [h0, h1, h1380, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1382 | h1382
      · linarith only [h1380, h1382, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1384 | h1384
        · linarith only [h1380, h1384, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1386 | h1386
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1387 | h1387
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1388 | h1388
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1389 | h1389
                · linarith only [h0, h1, h1380, h1389, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h1389, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1392 | h1392
                · linarith only [h0, h1, h1392, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1, h1392, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h1387, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h1386, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1397 | h1397
    · linarith only [h0, h1, h1397, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1399 | h1399
      · linarith only [h1397, h1399, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1401 | h1401
        · linarith only [h1397, h1401, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1403 | h1403
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1404 | h1404
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1405 | h1405
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
                · linarith only [h0, h1, h1397, h1406, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h1406, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1409 | h1409
                · linarith only [h0, h1, h1409, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1, h1409, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h1404, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h1403, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0 m hb0 hb2 hb5 h0 h1
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x1 m hb0 hb2 hb5 h0 h1

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  exact r1l7_10_12_25_L_I_L_R_H_I_s0 m hb0 hb2 hb5 h0

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0 m hb0 hb2 hb5 h0
  · exact r1l7_10_12_25_L_I_L_R_H_I_x1 m hb0 hb2 hb5 h0

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 1 5 (by decide) (by decide) with h2723 | h2723
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2724 | h2724
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2725 | h2725
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2726 | h2726
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2727 | h2727
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2728 | h2728
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2729 | h2729
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2730 | h2730
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2731 | h2731
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2732 | h2732
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2733 | h2733
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2734 | h2734
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2735 | h2735
                          · linarith only [h2722, h2735, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2737 | h2737
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2738 | h2738
                              · linarith only [h2724, h2738, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h1833, h2722, h2724, h2729, h2734, h2735, h2737, h2738, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h1833, h2722, h2724, h2729, h2733, h2735, h2737, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1833, h2722, h2729, h2734, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h1833, h2722, h2729, h2733, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h0, h2722, h2729, h2732, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h1833, h2722, h2729, h2730, h2731, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h2722, h2729, h2730, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2747 | h2747
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2748 | h2748
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2749 | h2749
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2750 | h2750
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2751 | h2751
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2752 | h2752
                          · linarith only [h2722, h2729, h2752, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2754 | h2754
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2755 | h2755
                              · linarith only [h2724, h2755, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h2724, h2728, h2754, h2755, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2758 | h2758
                              · linarith only [h1833, h2723, h2724, h2750, h2752, h2754, h2758, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2760 | h2760
                                · linarith only [h2722, h2729, h2750, h2754, h2760, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2762 | h2762
                                  · linarith only [h2722, h2729, h2750, h2762, hlam]
                                  · rcases h0bigk with h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1833, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1833, h2722, h2724, h2750, h2754, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2764_1, u0elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1833, h2724, hlam, hphi, ht0b, ht5b, p2764_1, u0elo1, u5ehi0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2723, hlam, hphi, ht0b, ht5b, p2764_1, u0elo1, u5ehi1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1833, h2723, hlam, hphi, ht0b, ht5b, p2764_1, u0elo1, u5ehi1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2722, h2750, h2754, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2764_1, u0elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2723, hlam, hphi, ht0b, ht5b, p2764_1, u0elo1, u5ehi1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2722, h2750, h2754, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2764_1, u0elo2]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2724, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2722, h2724, h2750, h2754, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2764_1, u0elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2724, hlam, hphi, ht0b, ht5b, p2764_1, u0elo1, u5ehi0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2722, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2725, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2727, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2729, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2723, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2726, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2728, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2722, h2750, h2754, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2764_1, u0elo4]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                        · linarith only [h1833, h2723, h2749, h2751, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h1833, h2723, h2749, h2750, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1833, h2723, h2747, h2749, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h1833, h2723, h2747, h2748, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h2723, h2747, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1833, h2723, h2728, hlam]
          · linarith only [h1833, h2722, h2727, hlam]
        · linarith only [h0, h2723, h2726, hlam]
      · linarith only [h1833, h2722, h2724, h2725, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2799 | h2799
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2800 | h2800
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2801 | h2801
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2802 | h2802
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2803 | h2803
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2804 | h2804
                · linarith only [h2724, h2800, h2804, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h2722, h2803, h2804, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2807 | h2807
                · linarith only [h0, h2723, h2724, h2807, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h2723, h2807, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h2723, h2724, h2802, hlam]
          · linarith only [h0, h2722, h2724, h2801, hlam]
        · linarith only [h0, h2723, h2800, hlam]
      · linarith only [h0, h2722, h2799, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2814 | h2814
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2815 | h2815
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2816 | h2816
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2817 | h2817
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2818 | h2818
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2819 | h2819
              · linarith only [h2722, h2723, h2819, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2821 | h2821
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2822 | h2822
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2823 | h2823
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2824 | h2824
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2825 | h2825
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2826 | h2826
                          · linarith only [h2722, h2723, h2814, h2818, h2819, h2826, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2828 | h2828
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2829 | h2829
                              · linarith only [h2814, h2829, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h2818, h2828, h2829, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h2722, h2723, h2824, h2826, h2828, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1833, h2814, h2818, h2825, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1833, h2817, h2824, hlam]
                    · linarith only [h0, h2722, h2816, h2822, h2823, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · linarith only [h0, h2815, h2822, hlam]
                · linarith only [h0, h2814, h2821, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2838 | h2838
              · linarith only [h2722, h2723, h2838, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2840 | h2840
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2841 | h2841
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2842 | h2842
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2843 | h2843
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2844 | h2844
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2845 | h2845
                          · linarith only [h1833, h2722, h2818, h2838, h2840, h2844, h2845, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2847 | h2847
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2848 | h2848
                              · linarith only [h1833, h2814, h2818, h2848, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2850 | h2850
                                · linarith only [h1833, h2722, h2818, h2841, h2844, h2845, h2850, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2852 | h2852
                                  · linarith only [h1833, h2722, h2818, h2841, h2844, h2845, h2847, h2852, hlam]
                                  · rcases h0bigk with h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c | h2854c
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h0, hlam, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h1833, hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h1833, h2722, h2818, h2840, h2841, h2844, h2847, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2723, hlam, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2722, h2841, h2847, hc34, hlam, hphi, ht0b, ht45, ht5b, p2854_1, u0elo1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h1833, h2722, h2841, h2847, hc34, hlam, hphi, ht0b, ht45, ht5b, p2854_1, u0elo1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      rcases p2854_3 (m.d 0 1) (by simp) with h2863 | h2863
                                      · linarith only [h0, h2863, hlam]
                                      · linarith only [h2722, h2863, hlam]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h1833, h2722, h2818, h2841, h2847, hc34, hlam, hphi, ht0b, ht45, ht5b, p2854_1, u0elo1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2722, h2841, h2847, hc34, hlam, hphi, ht0b, ht45, ht5b, p2854_1, u0elo2]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2814, hlam, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2722, h2818, h2840, h2841, h2844, h2847, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2818, hlam, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2722, hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2815, hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2817, hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2838, hlam, p2854_0]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2722, h2816, h2841, h2847, hc34, hlam, hphi, ht0b, ht45, ht5b, p2854_1, u0elo1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h2816, hlam, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [h1833, h2722, h2818, h2840, h2841, h2844, h2847, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2854_1]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      rcases p2854_3 (m.d 0 1) (by simp) with h2880 | h2880
                                      · linarith only [h2723, h2880, hlam]
                                      · linarith only [h2722, h2880, hlam]
                                    · have p2854_0 := h2854c.1
                                      have p2854_1 := h2854c.2.1
                                      have p2854_2 := h2854c.2.2.1
                                      have p2854_3 := h2854c.2.2.2
                                      linarith only [hlam, p2854_0]
                            · linarith only [h2817, h2818, h2840, h2844, h2847, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2885 | h2885
                          · linarith only [h1833, h2722, h2844, h2885, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2887 | h2887
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2888 | h2888
                              · linarith only [h1833, h2844, h2888, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2890 | h2890
                                · linarith only [h1833, h2722, h2723, h2841, h2844, h2885, h2890, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2892 | h2892
                                  · linarith only [h1833, h2722, h2841, h2844, h2885, h2887, h2892, hlam]
                                  · linarith only [h1833, h2722, h2841, h2844, h2887, h2892, hc34, hc45, hlam, hphi]
                            · linarith only [h1833, h2817, h2844, h2887, hc23, hc35, hlam, hphi]
                      · linarith only [h1833, h2722, h2817, h2841, h2843, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2722, h2816, h2841, h2842, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2815, h2841, hlam]
                · linarith only [h0, h2814, h2840, hlam]
          · linarith only [h1833, h2722, h2817, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2901 | h2901
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2902 | h2902
            · linarith only [h2814, h2816, h2902, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2904 | h2904
              · linarith only [h2722, h2723, h2904, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2906 | h2906
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2907 | h2907
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2908 | h2908
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2909 | h2909
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2910 | h2910
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2911 | h2911
                          · linarith only [h2722, h2904, h2911, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2913 | h2913
                            · linarith only [h2814, h2816, h2908, h2913, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1833, h2722, h2814, h2816, h2908, h2909, h2913, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2916 | h2916
                          · linarith only [h1833, h2722, h2814, h2816, h2908, h2916, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2918 | h2918
                            · linarith only [h2814, h2816, h2908, h2918, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2814, h2816, h2901, h2908, h2918, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1833, h2814, h2816, h2901, h2908, h2909, hc01, hc12, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2922 | h2922
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2923 | h2923
                        · linarith only [h1833, h2902, h2906, h2908, h2923, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2925 | h2925
                          · linarith only [h1833, h2722, h2904, h2923, h2925, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2927 | h2927
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2928 | h2928
                              · linarith only [h1833, h2814, h2923, h2928, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2930 | h2930
                                · linarith only [h1833, h2722, h2906, h2907, h2908, h2925, h2928, h2930, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · linarith only [h1833, h2722, h2906, h2907, h2908, h2927, h2930, hc34, hc45, hlam, hphi]
                            · linarith only [h2901, h2902, h2927, hc23, hc35, hlam, hphi]
                      · linarith only [h1833, h2901, h2902, h2922, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2815, h2907, hlam]
                · linarith only [h0, h2814, h2906, hlam]
          · linarith only [h1833, h2722, h2901, hlam]
      · linarith only [h0, h2722, h2815, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2939 | h2939
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2940 | h2940
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2941 | h2941
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2942 | h2942
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2943 | h2943
              · linarith only [h2722, h2723, h2943, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2945 | h2945
                · linarith only [h2814, h2940, h2945, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2947 | h2947
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2948 | h2948
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2949 | h2949
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2950 | h2950
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2951 | h2951
                          · linarith only [h2722, h2943, h2951, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2953 | h2953
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2954 | h2954
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2955 | h2955
                                · linarith only [h2722, h2723, h2947, h2951, h2955, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2957 | h2957
                                  · linarith only [h2722, h2723, h2947, h2951, h2953, h2957, hlam]
                                  · rcases h0bigk with h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c | h2959c
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h0, hlam, p2959_1]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h1833, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2723, h2945, h2948, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2959_1]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2723, hlam, p2959_1]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h0, h2945, hc01, hc23, hlam, hphi, ht12, p2959_1]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2814, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      rcases p2959_3 (m.d 0 1) (by simp) with h2968 | h2968
                                      · linarith only [h0, h2968, hlam]
                                      · linarith only [h2722, h2968, hlam]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h0, h2945, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2959_1, u5ehi0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2722, h2947, h2953, hc34, hlam, hphi, ht0b, ht45, ht5b, p2959_1, u0elo2]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h0, h2722, h2947, h2953, hc34, hlam, hphi, ht0b, ht45, ht5b, p2959_1, u0elo2]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      rcases p2959_3 (m.d 0 1) (by simp) with h2975 | h2975
                                      · linarith only [h1833, h2975, hlam]
                                      · linarith only [h2722, h2975, hlam]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2722, h2723, h2947, h2953, hc34, hlam, hphi, ht0b, ht45, ht5b, p2959_1, u0elo2]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2722, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2939, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2941, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2943, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2722, h2947, h2953, hc34, hlam, hphi, ht0b, ht45, ht5b, p2959_1, u0elo4]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2940, hlam, p2959_1]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [h2942, hlam, p2959_0]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      rcases p2959_3 (m.d 0 1) (by simp) with h2987 | h2987
                                      · linarith only [h2723, h2987, hlam]
                                      · linarith only [h2722, h2987, hlam]
                                    · have p2959_0 := h2959c.1
                                      have p2959_1 := h2959c.2.1
                                      have p2959_2 := h2959c.2.2.1
                                      have p2959_3 := h2959c.2.2.2
                                      linarith only [hlam, p2959_0]
                              · linarith only [h0, h2722, h2945, h2947, h2953, h2954, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h2945, h2953, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1833, h2942, h2950, hlam]
                      · linarith only [h1833, h2941, h2949, hlam]
                    · linarith only [h0, h2940, h2948, hlam]
                  · linarith only [h0, h2939, h2947, hlam]
            · linarith only [h2814, h2940, h2942, hlam]
          · linarith only [h0, h2722, h2814, h2941, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2999 | h2999
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3000 | h3000
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3001 | h3001
              · linarith only [h0, h2722, h2940, h3001, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3003 | h3003
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3004 | h3004
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3005 | h3005
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3006 | h3006
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3007 | h3007
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3008 | h3008
                          · linarith only [h0, h2722, h2814, h3001, h3003, h3008, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3010 | h3010
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3011 | h3011
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3012 | h3012
                                · linarith only [h0, h2722, h2940, h3004, h3005, h3008, h3012, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3014 | h3014
                                  · linarith only [h0, h2722, h2940, h3004, h3005, h3008, h3010, h3014, hlam]
                                  · rcases h0bigk with h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c | h3016c
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h0, hlam, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h1833, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h0, h2940, h3003, h3011, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2723, hlam, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2940, h3003, h3011, hc01, hc12, hlam, hphi, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2814, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2722, h2940, h3003, h3004, h3010, h3011, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2940, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2722, h3004, h3010, hc34, hlam, hphi, ht0b, ht45, ht5b, p3016_1, u0elo2]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h0, h2722, h2814, h3003, h3004, h3010, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      rcases p3016_3 (m.d 0 1) (by simp) with h3030 | h3030
                                      · linarith only [h1833, h3030, hlam]
                                      · linarith only [h2722, h3030, hlam]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h0, h2722, h2814, h2940, h3003, h3004, h3010, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2722, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2939, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2999, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h3001, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h2722, h3004, h3010, hc34, hlam, hphi, ht0b, ht45, ht5b, p3016_1, u0elo4]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h0, h2722, h2940, h3003, h3004, h3010, h3011, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3016_1]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [h3000, hlam, p3016_0]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      rcases p3016_3 (m.d 0 1) (by simp) with h3042 | h3042
                                      · linarith only [h2723, h3042, hlam]
                                      · linarith only [h2722, h3042, hlam]
                                    · have p3016_0 := h3016c.1
                                      have p3016_1 := h3016c.2.1
                                      have p3016_2 := h3016c.2.2.1
                                      have p3016_3 := h3016c.2.2.2
                                      linarith only [hlam, p3016_0]
                              · linarith only [h2814, h3000, h3011, hlam]
                            · linarith only [h2814, h2999, h3010, hlam]
                        · linarith only [h1833, h2722, h3000, h3004, h3007, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h2814, h2999, h3003, h3006, hlam]
                    · linarith only [h0, h2722, h2814, h3003, h3004, h3005, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2722, h2814, h3003, h3004, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3052 | h3052
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3053 | h3053
                    · linarith only [h0, h2722, h2940, h3003, h3052, h3053, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3055 | h3055
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3056 | h3056
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3057 | h3057
                          · linarith only [h2722, h3057, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3059 | h3059
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3060 | h3060
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3061 | h3061
                                · linarith only [h0, h2939, h3053, h3057, h3061, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h0, h2722, h3052, h3053, h3059, h3061, hc34, hc45, hlam, hphi]
                              · linarith only [h2814, h3000, h3060, hlam]
                            · linarith only [h0, h3003, h3059, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1833, h3000, h3056, hlam]
                      · linarith only [h1833, h2999, h3055, hlam]
                  · linarith only [h0, h2939, h3052, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3069 | h3069
              · linarith only [h2722, h2723, h3069, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3071 | h3071
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3072 | h3072
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3073 | h3073
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3074 | h3074
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3075 | h3075
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3076 | h3076
                          · linarith only [h0, h2722, h2814, h3000, h3069, h3071, h3075, h3076, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3078 | h3078
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3079 | h3079
                              · linarith only [h0, h2814, h3000, h3071, h3079, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h2722, h2814, h3071, h3072, h3075, h3078, h3079, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h2722, h2814, h2999, h3072, h3078, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3083 | h3083
                          · linarith only [h2722, h3083, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3085 | h3085
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3086 | h3086
                              · linarith only [h3071, h3075, h3086, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3088 | h3088
                                · linarith only [h0, h2722, h2814, h3071, h3072, h3075, h3083, h3088, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3090 | h3090
                                  · linarith only [h0, h2722, h2814, h3071, h3072, h3075, h3083, h3085, h3090, hlam]
                                  · linarith only [h0, h2722, h2814, h3071, h3075, h3090, hc14, hc45, hlam, hphi]
                            · linarith only [h0, h2722, h2814, h2999, h3072, h3085, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h2722, h2814, h2999, h3071, h3072, h3074, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2722, h2814, h3071, h3072, h3073, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2722, h2814, h3071, h3072, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3097 | h3097
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3098 | h3098
                    · linarith only [h0, h2722, h2940, h3071, h3097, h3098, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3100 | h3100
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3101 | h3101
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3102 | h3102
                          · linarith only [h2722, h3102, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3104 | h3104
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3105 | h3105
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3106 | h3106
                                · linarith only [h0, h2722, h2814, h3000, h3071, h3097, h3098, h3101, h3102, h3106, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h2722, h3097, h3098, h3104, h3106, hc34, hc45, hlam, hphi]
                              · linarith only [h3071, h3101, h3105, hlam]
                            · linarith only [h0, h2722, h2814, h3000, h3071, h3097, h3101, h3104, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3111 | h3111
                          · linarith only [h0, h2722, h3071, h3101, h3111, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3113 | h3113
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3114 | h3114
                              · linarith only [h0, h2722, h3071, h3097, h3101, h3113, h3114, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h2722, h3071, h3097, h3113, h3114, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h2722, h3071, h3097, h3113, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h2722, h2999, h3071, h3100, hlam]
                  · linarith only [h0, h2939, h3097, hlam]
          · linarith only [h1833, h2722, h2999, hlam]
      · linarith only [h0, h2722, h2939, hlam]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 3 (by decide) (by decide) with h3123 | h3123
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3124 | h3124
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3125 | h3125
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3126 | h3126
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3127 | h3127
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3128 | h3128
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3129 | h3129
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3130 | h3130
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3131 | h3131
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3132 | h3132
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3133 | h3133
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3134 | h3134
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3135 | h3135
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3136 | h3136
                            · linarith only [h3123, h3136, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                            · linarith only [h3123, h3127, h3135, h3136, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3139 | h3139
                            · linarith only [h3123, h3139, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3141 | h3141
                              · linarith only [h3123, h3126, h3135, h3141, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3143 | h3143
                                · linarith only [h3123, h3126, h3135, h3141, h3143, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h3123, h3126, h3128, h3135, h3143, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h2722, h3123, h3126, h3128, h3134, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h2722, h3122, h3131, h3132, h3133, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1833, h3122, h3131, h3132, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h3122, h3131, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h1833, h3122, h3129, h3130, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h3122, h3129, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h2722, h3122, h3128, hlam]
          · linarith only [h1833, h3122, h3127, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3154 | h3154
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3155 | h3155
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3156 | h3156
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3157 | h3157
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3158 | h3158
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3159 | h3159
                    · linarith only [h1833, h3122, h3126, h3156, h3158, h3159, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h1833, h3122, h3158, h3159, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h3122, h3158, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h1833, h3122, h3124, h3156, h3157, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
              · linarith only [h0, h3122, h3123, h3156, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
            · linarith only [h1833, h3122, h3126, h3155, hlam]
          · linarith only [h1833, h3122, h3154, hlam]
      · linarith only [h0, h3122, h3125, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3168 | h3168
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3169 | h3169
        · linarith only [h3123, h3124, h3169, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3171 | h3171
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3172 | h3172
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3173 | h3173
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3174 | h3174
                · linarith only [h1833, h3122, h3123, h3124, h3174, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h3122, h3174, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h3122, h3123, h3173, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
            · linarith only [h0, h3122, h3124, h3172, hlam]
          · linarith only [h1833, h3122, h3171, hlam]
      · linarith only [h1833, h3122, h3123, h3168, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3181 | h3181
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3182 | h3182
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3183 | h3183
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3184 | h3184
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3185 | h3185
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3186 | h3186
              · linarith only [h3123, h3182, h3186, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3122, h3186, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h2722, h3122, h3185, hlam]
          · linarith only [h2722, h3122, h3123, h3181, h3184, hlam]
        · linarith only [h3123, h3181, h3183, hlam]
      · linarith only [h2722, h3122, h3181, h3182, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3193 | h3193
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3194 | h3194
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3195 | h3195
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3196 | h3196
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3197 | h3197
              · linarith only [h3123, h3193, h3197, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3122, h3197, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h2722, h3122, h3196, hlam]
          · linarith only [h1833, h3122, h3195, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3202 | h3202
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3203 | h3203
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3204 | h3204
              · linarith only [h0, h3122, h3123, h3204, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h3122, h3204, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h3122, h3123, h3194, h3203, hlam]
          · linarith only [h0, h3122, h3123, h3202, hlam]
      · linarith only [h0, h3122, h3193, hlam]

end R2N4
