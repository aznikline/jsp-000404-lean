import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h1142 | h1142
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1145 | h1145
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1146 | h1146
          · linarith only [h1, h1146, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1148 | h1148
            · linarith only [h1145, h1146, h1148, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1150 | h1150
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1151 | h1151
                · linarith only [h1144, h1145, h1146, h1151, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1153 | h1153
                  · linarith only [h1143, h1148, h1153, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1155 | h1155
                    · linarith only [h1145, h1148, h1155, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h1142, h1155, h4, hlam]
              · linarith only [h1145, h1146, h1150, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1159 | h1159
          · linarith only [h0, h1145, h1159, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1161 | h1161
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1162 | h1162
              · linarith only [h1143, h1145, h1162, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1164 | h1164
                · linarith only [h1162, h1164, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1166 | h1166
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1167 | h1167
                    · rcases h5bigk with h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1, h1144, h1164, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1168_1, u1elo0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1, h1164, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1168_1, u1elo0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h4, hlam, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h0, h1142, hc45, hlam, hphi, ht01, ht0b, ht5b, p1168_1, u1elo0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1, hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1164, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1168_1, u1elo4]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1159, hlam, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h0, h1161, hc45, hlam, hphi, ht01, ht0b, ht5b, p1168_1, u1elo0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h3, hlam, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1144, hlam, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1164, hlam, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h4, hc03, hc35, hlam, hphi, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1159, hc13, hc35, hlam, hphi, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1164, hc23, hc35, hlam, hphi, p1168_1]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        rcases p1168_3 (m.d 0 5) (by simp) with h1188 | h1188
                        · linarith only [h1188, h4, hlam]
                        · linarith only [h1142, h1188, hlam]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1142, hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1161, hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1166, hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [h1167, hlam, p1168_0]
                      · have p1168_0 := h1168c.1
                        have p1168_1 := h1168c.2.1
                        have p1168_2 := h1168c.2.2.1
                        have p1168_3 := h1168c.2.2.2
                        linarith only [hlam, p1168_0]
                    · linarith only [h0, h1142, h1145, h1167, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h1161, h1166, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1198 | h1198
              · linarith only [h0, h1142, h1143, h1145, h1161, h1198, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1200 | h1200
                · linarith only [h1198, h1200, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                  · linarith only [h1143, h1161, h1202, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1204 | h1204
                    · rcases h5bigk with h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c | h1205c
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h0, h1142, hc15, hlam, hphi, ht01, ht0b, ht5b, p1205_1, u1elo0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h0, h1142, h1198, h1202, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1205_1, u1elo0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h4, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h0, h1142, h1161, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1205_1, u1elo0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1, hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1198, h1202, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1205_1, u1elo4]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1159, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1161, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h3, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1144, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1200, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1202, hlam, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1198, h1202, h3, hc23, hc35, hlam, hphi, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1144, h1198, h1202, hc23, hc35, hlam, hphi, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1198, h1202, hc23, hc35, hlam, hphi, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1143, h1161, h1198, h1204, hc23, hc34, hlam, hphi, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1142, hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1144, h1198, h1202, hc23, hc45, hlam, hphi, ht34, p1205_1]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h0, h1142, h1198, h1202, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1205_1, u1elo0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [h1204, hlam, p1205_0]
                      · have p1205_0 := h1205c.1
                        have p1205_1 := h1205c.2.1
                        have p1205_2 := h1205c.2.2.1
                        have p1205_3 := h1205c.2.2.2
                        linarith only [hlam, p1205_0]
                    · linarith only [h0, h1142, h1145, h1204, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
          · linarith only [h1143, h1144, h1233, h3, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1235 | h1235
            · linarith only [h1143, h1144, h1235, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1237 | h1237
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1238 | h1238
                · linarith only [h1238, h3, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1240 | h1240
                  · linarith only [h1143, h1144, h1235, h1240, h3, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1142, h1143, h1144, h1237, h1240, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h1142, h1232, h1233, h1235, h1237, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1244 | h1244
          · linarith only [h1232, h1244, h4, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1246 | h1246
            · linarith only [h1143, h1144, h1246, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1248 | h1248
              · linarith only [h1, h1143, h1144, h1232, h1248, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1250 | h1250
                · linarith only [h1144, h1248, h1250, h3, h4, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1252 | h1252
                  · linarith only [h1143, h1144, h1232, h1246, h1252, h3, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1142, h1143, h1144, h1248, h1252, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1255 | h1255
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1256 | h1256
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1257 | h1257
          · linarith only [h1, h1257, h4, hlam]
          · linarith only [h1143, h1255, h1256, h1257, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1260 | h1260
          · linarith only [h1256, h1260, h4, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1262 | h1262
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1263 | h1263
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1264 | h1264
                · linarith only [h1143, h1255, h1260, h1264, h2, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h1256, h1263, h1264, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1267 | h1267
                · linarith only [h1263, h1267, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1269 | h1269
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1270 | h1270
                    · rcases h5bigk with h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1271_1, u1elo0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1, h1267, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1271_1, u1elo0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h4, hlam, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p1271_1, u1elo0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1, hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1267, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1271_1, u1elo4]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1260, hlam, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1255, hc45, hlam, hphi, ht01, ht0b, ht5b, p1271_1, u1elo1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h3, hlam, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1255, hlam, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1267, hlam, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h0, h1143, h1255, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1271_1, u1elo0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1267, h3, hc23, hc35, hlam, hphi, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1255, h1267, hc23, hc35, hlam, hphi, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1267, hc23, hc35, hlam, hphi, p1271_1]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        rcases p1271_3 (m.d 0 5) (by simp) with h1291 | h1291
                        · linarith only [h1291, h4, hlam]
                        · linarith only [h1142, h1291, hlam]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1142, hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1262, hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1269, hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [h1270, hlam, p1271_0]
                      · have p1271_0 := h1271c.1
                        have p1271_1 := h1271c.2.1
                        have p1271_2 := h1271c.2.2.1
                        have p1271_3 := h1271c.2.2.2
                        linarith only [hlam, p1271_0]
                    · linarith only [h0, h1142, h1256, h1270, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1143, h1255, h1262, h1267, h1269, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
            · linarith only [h0, h1142, h1143, h1255, h1262, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1303 | h1303
          · linarith only [h1, h1303, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1305 | h1305
            · linarith only [h1302, h1303, h1305, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1307 | h1307
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1308 | h1308
                · linarith only [h1308, h3, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1310 | h1310
                  · linarith only [h1143, h1305, h1307, h1308, h1310, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1142, h1143, h1310, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h1142, h1302, h1303, h1305, h1307, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1314 | h1314
          · linarith only [h1302, h1314, h4, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1318 | h1318
                · linarith only [h1318, h3, h4, hlam]
                · linarith only [h1302, h1317, h1318, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1321 | h1321
                · linarith only [h1317, h1321, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1323 | h1323
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1324 | h1324
                    · rcases h5bigk with h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1325_1, u1elo0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1, h1255, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1325_1, u1elo0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h4, hlam, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h0, h1142, hc45, hlam, hphi, ht01, ht0b, ht5b, p1325_1, u1elo0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1, hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1255, hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1314, hlam, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p1325_1, u1elo4]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h3, hlam, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1323, h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1321, hlam, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h0, h1323, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1325_1, u1elo0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1, h1255, hc12, hc35, hlam, hphi, ht23, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1255, hc12, hc35, hlam, hphi, ht23, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1255, hc12, hc35, hlam, hphi, ht23, p1325_1]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        rcases p1325_3 (m.d 0 5) (by simp) with h1345 | h1345
                        · linarith only [h1345, h4, hlam]
                        · linarith only [h1142, h1345, hlam]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1142, hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1316, hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1323, hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [h1324, hlam, p1325_0]
                      · have p1325_0 := h1325c.1
                        have p1325_1 := h1325c.2.1
                        have p1325_2 := h1325c.2.2.1
                        have p1325_3 := h1325c.2.2.2
                        linarith only [hlam, p1325_0]
                    · linarith only [h0, h1316, h1324, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h1143, h1316, h1323, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1355 | h1355
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1356 | h1356
                · linarith only [h1356, h3, h4, hlam]
                · linarith only [h1302, h1355, h1356, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1359 | h1359
                · linarith only [h1355, h1359, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1361 | h1361
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
                    · rcases h5bigk with h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1363_1, u1elo0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1, h1316, h1361, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1363_1, u1elo0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h4, hlam, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h0, h1142, h1316, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1363_1, u1elo0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1, hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1255, hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1314, hlam, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1316, hlam, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h3, hlam, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1359, hlam, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h0, h1142, h1143, h1316, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1363_1, u1elo0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1, h1143, h1316, hc12, hc35, hlam, hphi, ht23, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1143, h1316, hc12, hc35, hlam, hphi, ht23, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1255, hc12, hc35, hlam, hphi, ht23, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1143, h1316, h1362, hc12, hc34, hlam, hphi, ht23, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1142, hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1143, h1316, h1361, hc12, hc25, hlam, hphi, p1363_1]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1361, hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [h1362, hlam, p1363_0]
                      · have p1363_0 := h1363c.1
                        have p1363_1 := h1363c.2.1
                        have p1363_2 := h1363c.2.2.1
                        have p1363_3 := h1363c.2.2.2
                        linarith only [hlam, p1363_0]
                    · linarith only [h0, h1302, h1361, h1362, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h1142, h1143, h1361, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1391 | h1391
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1392 | h1392
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1393 | h1393
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1394 | h1394
          · linarith only [h1, h1394, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1396 | h1396
            · linarith only [h0, h1142, h1396, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1398 | h1398
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1399 | h1399
                · linarith only [h1, h1392, h1393, h1394, h1399, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1401 | h1401
                  · linarith only [h0, h1142, h1391, h1401, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1403 | h1403
                    · linarith only [h1, h1142, h1392, h1398, h1399, h1403, hlam]
                    · rcases h5bigk with h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [hlam, p1405_0]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1392, h1398, h1399, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1, h1398, h1399, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1405_1, u1elo0]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h4, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1142, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1, hlam, p1405_0]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [hlam, p1405_0]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1398, h1399, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1405_1, u1elo4]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1394, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1396, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h3, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1392, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [hlam, p1405_0]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1399, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1401, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1398, h1399, h1403, h3, hc34, hc45, hlam, hphi, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1392, h1398, h1399, h1403, hc34, hc45, hlam, hphi, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1398, h1399, h1403, hc34, hc45, hlam, hphi, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [hlam, p1405_0]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1403, hlam, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1, h1392, h1398, h1399, hc34, hc45, hlam, hphi, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1392, h1398, h1399, hc34, hc45, hlam, hphi, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h1398, h1399, hc34, hc45, hlam, hphi, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [h4, hc03, hc45, hlam, hphi, ht34, p1405_1]
                      · have p1405_0 := h1405c.1
                        have p1405_1 := h1405c.2.1
                        have p1405_2 := h1405c.2.2.1
                        have p1405_3 := h1405c.2.2.2
                        linarith only [hlam, p1405_0]
              · linarith only [h1393, h1394, h1398, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1432 | h1432
          · linarith only [h1393, h1432, h4, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1434 | h1434
            · linarith only [h0, h1142, h1434, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1436 | h1436
              · linarith only [h1391, h1393, h1436, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1438 | h1438
                · linarith only [h1436, h1438, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1440 | h1440
                  · linarith only [h0, h1142, h1391, h1440, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1442 | h1442
                    · rcases h5bigk with h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1, h1391, h1434, h1436, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1443_1, u1elo0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1, h1436, h1440, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1443_1, u1elo0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h4, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1142, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1, hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1436, h1440, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1443_1, u1elo4]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1432, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1434, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h3, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1392, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1438, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1440, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1436, h1440, h3, hc23, hc35, hlam, hphi, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1392, h1436, h1440, hc23, hc35, hlam, hphi, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1436, h1440, hc23, hc35, hlam, hphi, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, h1142, h1391, h1436, h1442, hc23, hc34, hlam, hphi, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, h1142, h1391, h1436, hc23, hc45, hlam, hphi, ht34, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1392, h1436, h1440, hc23, hc45, hlam, hphi, ht34, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1436, h1440, hc23, hc45, hlam, hphi, ht34, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1442, hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                    · rcases h5bigk with h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c | h1469c
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [hlam, p1469_0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1, h1392, h1436, h1440, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1469_1, u1elo0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1, h1436, h1440, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1469_1, u1elo0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h4, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1142, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1, hlam, p1469_0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [hlam, p1469_0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1436, h1440, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1469_1, u1elo4]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1432, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1434, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h3, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1392, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [hlam, p1469_0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1438, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1440, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1436, h1440, h1442, h3, hc23, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1392, h1436, h1440, h1442, hc23, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1436, h1440, h1442, hc23, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [hlam, p1469_0]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1442, hlam, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h0, h1142, h1391, h1436, hc23, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1392, h1436, h1440, hc23, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h1436, h1440, hc23, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [h4, hc03, hc45, hlam, hphi, ht34, p1469_1]
                      · have p1469_0 := h1469c.1
                        have p1469_1 := h1469c.2.1
                        have p1469_2 := h1469c.2.2.1
                        have p1469_3 := h1469c.2.2.2
                        linarith only [hlam, p1469_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1495 | h1495
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1496 | h1496
          · linarith only [h1391, h1392, h1496, h3, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1498 | h1498
            · linarith only [h0, h1142, h1498, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1500 | h1500
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1501 | h1501
                · linarith only [h1501, h3, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1503 | h1503
                  · linarith only [h1142, h1391, h1392, h1503, h3, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                    · linarith only [h1142, h1391, h1392, h1500, h1505, h3, hlam]
                    · rcases h5bigk with h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1, h1391, h1392, h1500, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1, u1elo0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h4, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1142, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1392, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1496, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1498, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h3, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1501, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1503, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1, h1391, h1392, h1500, h1505, hc34, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, h1505, hc34, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, h1505, hc34, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1505, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, h3, hc34, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, hc34, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1391, h1392, h1500, hc34, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1501, hc23, hc45, hlam, hphi, ht34, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
              · linarith only [h1, h1495, h1496, h1500, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1534 | h1534
          · linarith only [h1495, h1534, h4, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1536 | h1536
            · linarith only [h0, h1142, h1536, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1538 | h1538
              · linarith only [h1, h1391, h1392, h1495, h1538, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1540 | h1540
                · linarith only [h1391, h1392, h1538, h1540, h3, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1542 | h1542
                  · linarith only [h1142, h1391, h1392, h1542, h3, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1544 | h1544
                    · linarith only [h1142, h1391, h1392, h1538, h1544, h3, hc23, hc34, hlam, hphi]
                    · rcases h5bigk with h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [hlam, p1546_0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1546_1, u1elo0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1, h1391, h1392, h1538, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1546_1, u1elo0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h4, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1142, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1, hlam, p1546_0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [hlam, p1546_0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1392, hlam, p1546_0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1534, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1536, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h3, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [hlam, p1546_0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1540, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1542, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1544, h4, hc03, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1391, h1392, h1538, h1544, hc23, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1391, h1392, h1538, h1544, hc23, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [hlam, p1546_0]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1544, hlam, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1391, h1392, h1538, h3, hc23, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1391, h1392, h1538, hc23, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h1391, h1392, h1538, hc23, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [h4, hc03, hc45, hlam, hphi, ht34, p1546_1]
                      · have p1546_0 := h1546c.1
                        have p1546_1 := h1546c.2.1
                        have p1546_2 := h1546c.2.2.1
                        have p1546_3 := h1546c.2.2.2
                        linarith only [hlam, p1546_0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1572 | h1572
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1573 | h1573
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1574 | h1574
          · linarith only [h1142, h1391, h1572, h1574, h2, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · linarith only [h1142, h1391, h1572, h1573, h1574, h2, hc34, hc45, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1577 | h1577
          · linarith only [h1142, h1391, h1572, h1577, h2, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1579 | h1579
            · linarith only [h0, h1142, h1391, h1572, h1579, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1391, h1572, h1579, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1582 | h1582
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1583 | h1583
          · linarith only [h1, h1583, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1585 | h1585
            · linarith only [h0, h1142, h1585, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1587 | h1587
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1588 | h1588
                · linarith only [h1588, h3, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1590 | h1590
                  · linarith only [h1142, h1590, h2, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1592 | h1592
                    · linarith only [h1142, h1391, h1592, h2, hc12, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1582, h1583, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1, h1391, h1587, h1588, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h4, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1142, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1572, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1583, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1585, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h3, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1582, h1583, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1588, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1590, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1, h1582, h1583, h1592, hc34, hc45, hlam, hphi, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1582, h1583, h1592, hc34, hc45, hlam, hphi, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1572, h1592, hc12, hc45, hlam, hphi, ht23, ht34, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1592, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1, h1582, h1583, hc34, hc45, hlam, hphi, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1582, h1583, hc34, hc45, hlam, hphi, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1391, h1587, h1588, hc12, hc45, hlam, hphi, ht23, ht34, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h4, hc03, hc45, hlam, hphi, ht34, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
              · linarith only [h1582, h1583, h1587, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1621 | h1621
          · linarith only [h0, h1582, h1621, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1623 | h1623
            · linarith only [h1142, h1391, h1623, h2, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1625 | h1625
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1626 | h1626
                · linarith only [h1626, h3, h4, hlam]
                · linarith only [h1582, h1625, h1626, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1629 | h1629
                · linarith only [h1625, h1629, h4, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1631 | h1631
                  · linarith only [h1142, h1631, h2, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1633 | h1633
                    · linarith only [h1142, h1391, h1633, h2, hc12, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1635_1, u1elo0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p1635_1, u1elo0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h4, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1142, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1572, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1621, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1623, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h3, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1629, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1631, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h4, hc03, hc35, hlam, hphi, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1572, hc12, hc35, hlam, hphi, ht23, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1572, hc12, hc35, hlam, hphi, ht23, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1633, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1142, h1391, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1391, h1623, hc12, hc45, hlam, hphi, ht23, ht34, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1572, hc12, hc45, hlam, hphi, ht23, ht34, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h4, hc03, hc45, hlam, hphi, ht34, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0_x0 m hb1 hb5 hg0 hg1 h2 h3 h4
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0_x1 m hb1 hb5 hg0 hg1 h2 h3 h4

end R2N4
