import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1118 | h1118
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1119 | h1119
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1120 | h1120
      · linarith only [h0, h1120, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1122 | h1122
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1123 | h1123
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1124 | h1124
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1126 | h1126
                · linarith only [h0, h1118, h1126, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1128 | h1128
                  · linarith only [h0, h1118, h1125, h1128, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1130 | h1130
                    · rcases h0bigk with h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h0, hlam, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1120, h1125, h1130, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1131_1, u2elo1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1120, h1130, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1131_1, u2elo1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1120, hlam, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1118, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h0, h1125, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1131_1, u2elo1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h0, h1119, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1131_1, u2elo1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1131_1, u2elo1, u5ehi0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1118, hlam, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1122, hlam, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1119, h1126, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1126, hlam, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1119, hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1123, hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1125, hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1128, hlam, p1131_0]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1118, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1124, hlam, p1131_1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1120, h1130, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1131_1, u2elo1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [h1119, h1120, h1130, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1131_1, u2elo1]
                      · have p1131_0 := h1131c.1
                        have p1131_1 := h1131c.2.1
                        have p1131_2 := h1131c.2.2.1
                        have p1131_3 := h1131c.2.2.2
                        linarith only [hlam, p1131_0]
                    · linarith only [h0, h1130, hc01, hlam, hphi, ht12, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1158 | h1158
                · linarith only [h0, h1118, h1158, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1160 | h1160
                  · linarith only [h0, h1119, h1160, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1162 | h1162
                    · rcases h0bigk with h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h0, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1120, h1162, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1120, h1162, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1120, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht12, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h0, h1118, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h0, h1123, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1163_1, u2elo1, u5ehi0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1118, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1122, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1125, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1158, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1119, hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1123, hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1118, h1119, h1120, h1158, hc13, hc35, hlam, hphi, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1160, hlam, p1163_0]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1158, hc01, hc35, hlam, hphi, ht12, ht23, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1124, hlam, p1163_1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1118, h1120, h1162, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [h1120, h1162, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1163_1, u2elo1]
                      · have p1163_0 := h1163c.1
                        have p1163_1 := h1163c.2.1
                        have p1163_2 := h1163c.2.2.1
                        have p1163_3 := h1163c.2.2.2
                        linarith only [hlam, p1163_0]
                    · linarith only [h0, h1124, h1162, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1190 | h1190
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1191 | h1191
                · linarith only [h0, h1118, h1191, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1193 | h1193
                  · linarith only [h0, h1119, h1124, h1193, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1195 | h1195
                    · linarith only [h0, h1124, h1195, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1118, h1195, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1198 | h1198
                · linarith only [h0, h1119, h1190, h1198, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1200 | h1200
                  · linarith only [h0, h1119, h1124, h1200, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1202 | h1202
                    · linarith only [h0, h1124, h1202, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1118, h1202, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h0, h1119, h1123, hlam]
        · linarith only [h0, h1118, h1122, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1207 | h1207
      · linarith only [h0, h1207, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1209 | h1209
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1210 | h1210
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1211 | h1211
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1212 | h1212
              · linarith only [h1118, h1119, h1212, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1214 | h1214
                · linarith only [h0, h1118, h1214, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1216 | h1216
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1217 | h1217
                    · rcases h0bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [hlam, p1218_0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1207, h1217, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u2elo1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1119, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1207, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [hc01, hlam, hphi, ht12, p1218_1, u2elo0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [hlam, p1218_0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, h1118, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u2elo1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, h1216, hlam, hphi, ht01, ht0b, ht12, ht5b, p1218_1, u2elo1, u5ehi4]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1218_1, u2elo1, u5ehi0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1118, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1209, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [hlam, p1218_0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1212, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1214, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1118, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1210, hlam, p1218_0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, h1118, h1210, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u2elo1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [hlam, p1218_0]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, h1118, h1207, h1210, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u2elo1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1118, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1211, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h0, h1118, h1211, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u2elo1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [h1216, hlam, p1218_1]
                      · have p1218_0 := h1218c.1
                        have p1218_1 := h1218c.2.1
                        have p1218_2 := h1218c.2.2.1
                        have p1218_3 := h1218c.2.2.2
                        linarith only [hlam, p1218_0]
                    · linarith only [h0, h1118, h1217, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1245 | h1245
                    · rcases h0bigk with h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1118, h1207, h1245, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1119, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1207, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hc01, hlam, hphi, ht12, p1246_1, u2elo0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h1118, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1246_1, u2elo1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1246_1, u2elo1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1246_1, u2elo1, u5ehi0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1118, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1209, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1212, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1214, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1118, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1210, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h1118, h1210, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1246_1, u2elo1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1216, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1118, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1211, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1118, h1207, h1245, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1246_1, u2elo1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1207, h1245, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1246_1, u2elo1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                    · linarith only [h0, h1211, h1245, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1273 | h1273
              · linarith only [h1118, h1119, h1273, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1275 | h1275
                · linarith only [h0, h1118, h1275, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1277 | h1277
                  · linarith only [h1210, h1211, h1277, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1279 | h1279
                    · linarith only [h1118, h1119, h1210, h1211, h1279, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1118, h1279, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1282 | h1282
            · linarith only [h1210, h1282, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1284 | h1284
              · linarith only [h0, h1118, h1210, h1284, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1286 | h1286
                · linarith only [h0, h1118, h1210, h1286, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1288 | h1288
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1289 | h1289
                    · linarith only [h0, h1118, h1282, h1289, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1118, h1289, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1292 | h1292
                    · linarith only [h0, h1118, h1282, h1292, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1118, h1292, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
        · linarith only [h0, h1118, h1209, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1296 | h1296
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1297 | h1297
      · linarith only [h0, h1297, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1299 | h1299
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1300 | h1300
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1301 | h1301
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1302 | h1302
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1303 | h1303
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1304 | h1304
                  · linarith only [h0, h1296, h1304, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1306 | h1306
                    · rcases h0bigk with h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, hlam, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1118, hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1297, h1306, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1307_1, u2elo1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1297, hlam, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1296, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, h1303, hlam, hphi, ht01, ht0b, ht12, ht5b, p1307_1, u2elo1, u5ehi3]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, h1296, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1307_1, u2elo1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1307_1, u2elo1, u5ehi0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1296, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1299, hlam, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, h1296, h1299, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1307_1, u2elo1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, h1296, h1297, h1299, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1307_1, u2elo1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1296, hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1300, hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1302, hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1304, hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1296, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1301, hlam, p1307_1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h1303, hlam, p1307_0]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [h0, h1296, h1299, h1303, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1307_1, u2elo1]
                      · have p1307_0 := h1307c.1
                        have p1307_1 := h1307c.2.1
                        have p1307_2 := h1307c.2.2.1
                        have p1307_3 := h1307c.2.2.2
                        linarith only [hlam, p1307_0]
                    · linarith only [h0, h1296, h1306, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1334 | h1334
                  · linarith only [h0, h1296, h1334, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1336 | h1336
                    · rcases h0bigk with h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h0, hlam, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1118, hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1297, h1336, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1337_1, u2elo1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1297, hlam, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [hc01, hlam, hphi, ht12, p1337_1, u2elo0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1337_1, u2elo1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h0, h1296, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1337_1, u2elo1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1337_1, u2elo1, u5ehi0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1296, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1299, hlam, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h0, h1296, h1299, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1337_1, u2elo1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1303, hlam, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1296, hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1300, hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1302, hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1334, hlam, p1337_0]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1296, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1301, hlam, p1337_1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1297, h1336, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1337_1, u2elo1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [h1296, h1297, h1336, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1337_1, u2elo1]
                      · have p1337_0 := h1337c.1
                        have p1337_1 := h1337c.2.1
                        have p1337_2 := h1337c.2.2.1
                        have p1337_3 := h1337c.2.2.2
                        linarith only [hlam, p1337_0]
                    · linarith only [h0, h1301, h1336, hlam]
              · linarith only [h1118, h1296, h1302, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1365 | h1365
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1366 | h1366
                · linarith only [h1299, h1301, h1366, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1368 | h1368
                  · linarith only [h0, h1296, h1368, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1370 | h1370
                    · linarith only [h1118, h1299, h1301, h1370, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1296, h1370, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h1118, h1296, h1365, hlam]
          · linarith only [h1118, h1296, h1299, h1300, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1375 | h1375
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1376 | h1376
            · linarith only [h1299, h1376, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1378 | h1378
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1379 | h1379
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1380 | h1380
                  · linarith only [h0, h1296, h1380, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1382 | h1382
                    · linarith only [h0, h1376, h1382, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1296, h1382, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1385 | h1385
                  · linarith only [h0, h1296, h1385, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1387 | h1387
                    · linarith only [h0, h1296, h1376, h1387, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1296, h1387, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h1118, h1296, h1378, hlam]
          · linarith only [h0, h1296, h1375, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1392 | h1392
      · linarith only [h0, h1392, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1394 | h1394
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1395 | h1395
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1396 | h1396
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1397 | h1397
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1398 | h1398
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1399 | h1399
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1400 | h1400
                    · rcases h0bigk with h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h0, hlam, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1118, hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1296, hlam, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1392, hlam, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [hc01, hlam, hphi, ht12, p1401_1, u2elo0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1397, h1399, hc02, hlam, hphi, ht0b, ht5b, p1401_1, u5ehi0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h0, h1399, hlam, hphi, ht01, ht0b, ht12, ht5b, p1401_1, u2elo1, u5ehi0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1401_1, u2elo1, u5ehi0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1118, hc01, hc13, hlam, hphi, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1394, hlam, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h0, h1394, h1396, h1399, hlam, hphi, ht01, ht0b, ht12, ht5b, p1401_1, u2elo1, u5ehi2]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h0, h1394, h1396, hlam, hphi, ht01, ht0b, ht12, ht5b, p1401_1, u2elo1, u5ehi2]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1296, hc01, hc14, hlam, hphi, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1395, hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1397, hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h0, h1394, h1396, h1397, hlam, hphi, ht01, ht0b, ht12, ht5b, p1401_1, u2elo1, u5ehi2]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1392, h1400, hc01, hlam, hphi, ht12, p1401_1, u2elo1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1396, hlam, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1398, hlam, p1401_0]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [h1399, hlam, p1401_1]
                      · have p1401_0 := h1401c.1
                        have p1401_1 := h1401c.2.1
                        have p1401_2 := h1401c.2.2.1
                        have p1401_3 := h1401c.2.2.2
                        linarith only [hlam, p1401_0]
                    · linarith only [h0, h1400, hc01, hlam, hphi, ht12, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1428 | h1428
                    · rcases h0bigk with h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1118, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1296, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1392, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1398, hlam, hphi, ht01, ht0b, ht12, ht5b, p1429_1, u2elo1, u5ehi3]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1429_1, u2elo1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1429_1, u2elo1, u5ehi0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1118, hc01, hc13, hlam, hphi, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1394, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1296, h1394, hc01, hlam, hphi, ht12, p1429_1, u2elo1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1394, h1396, hlam, hphi, ht01, ht0b, ht12, ht5b, p1429_1, u2elo1, u5ehi2]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1399, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1395, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1397, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1399, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1392, h1428, hc01, hlam, hphi, ht12, p1429_1, u2elo1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1396, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1398, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1394, h1398, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1429_1, u2elo1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                    · linarith only [h0, h1428, hc01, hlam, hphi, ht12, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1456 | h1456
                  · linarith only [h1397, h1398, h1456, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1458 | h1458
                    · rcases h0bigk with h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c | h1459c
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h0, hlam, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1118, hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1296, hlam, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1392, hlam, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1459_1, u2elo1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1459_1, u2elo1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1459_1, u2elo1, u5ehi0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1118, hc01, hc13, hlam, hphi, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1394, hlam, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h0, h1296, h1394, hc01, hlam, hphi, ht12, p1459_1, u2elo1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1398, hlam, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1456, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1395, hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1397, hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1456, hlam, p1459_0]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1392, h1458, hc01, hlam, hphi, ht12, p1459_1, u2elo1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1396, hlam, p1459_1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1392, h1458, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1459_1, u2elo1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [h1296, h1392, h1458, hc01, hlam, hphi, ht12, p1459_1, u2elo1]
                      · have p1459_0 := h1459c.1
                        have p1459_1 := h1459c.2.1
                        have p1459_2 := h1459c.2.2.1
                        have p1459_3 := h1459c.2.2.2
                        linarith only [hlam, p1459_0]
                    · linarith only [h0, h1458, hc01, hlam, hphi, ht12, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1486 | h1486
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1487 | h1487
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1488 | h1488
                    · rcases h0bigk with h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1118, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1296, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1392, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1486, hlam, hphi, ht01, ht0b, ht12, ht5b, p1489_1, u2elo1, u5ehi3]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1397, h1486, hlam, hphi, ht01, ht0b, ht12, ht5b, p1489_1, u2elo1, u5ehi3]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1489_1, u2elo1, u5ehi0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1397, hc01, hc34, hlam, hphi, ht12, ht23, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1394, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1397, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1395, h1396, h1397, hlam, hphi, ht01, ht0b, ht12, ht5b, p1489_1, u2elo1, u5ehi2]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1395, hc01, hlam, hphi, ht12, p1489_1, u2elo1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1395, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1395, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1489_1, u2elo1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1395, h1396, hlam, hphi, ht01, ht0b, ht12, ht5b, p1489_1, u2elo1, u5ehi2]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1392, h1488, hc01, hlam, hphi, ht12, p1489_1, u2elo1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1396, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1486, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1487, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                    · linarith only [h0, h1395, h1487, h1488, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · linarith only [h1397, h1486, h1487, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1517 | h1517
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1518 | h1518
                    · rcases h0bigk with h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1118, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1296, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1392, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1519_1, u2elo1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1519_1, u2elo1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1519_1, u2elo1, u5ehi0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1486, hc01, hc35, hlam, hphi, ht12, ht23, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1394, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1397, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1486, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1296, hc01, hc14, hlam, hphi, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1395, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, h1395, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1519_1, u2elo1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, h1395, h1396, hlam, hphi, ht01, ht0b, ht12, ht5b, p1519_1, u2elo1, u5ehi2]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1392, h1518, hc01, hlam, hphi, ht12, p1519_1, u2elo1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1396, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1118, h1392, h1518, hc01, hlam, hphi, ht12, p1519_1, u2elo1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1517, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                    · linarith only [h0, h1518, hc01, hlam, hphi, ht12, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1546 | h1546
                    · rcases h0bigk with h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1118, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1296, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1392, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, h1118, hc01, hlam, hphi, ht12, p1547_1, u2elo1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1, u2elo1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1547_1, u2elo1, u5ehi0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1118, hc01, hc13, hlam, hphi, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1394, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1397, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1486, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1517, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1395, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1517, hc03, hc45, hlam, hphi, ht34, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1517, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1392, h1546, hc01, hlam, hphi, ht12, p1547_1, u2elo1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1396, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1118, h1392, h1546, hc01, hlam, hphi, ht12, p1547_1, u2elo1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1392, h1546, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1, u2elo1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                    · linarith only [h0, h1546, hc01, hlam, hphi, ht12, u2elo4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1574 | h1574
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1575 | h1575
                · linarith only [h1394, h1396, h1575, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1577 | h1577
                  · linarith only [h1395, h1396, h1577, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1579 | h1579
                    · linarith only [h1396, h1579, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1579, hc01, hlam, hphi, ht12, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1582 | h1582
                · linarith only [h1395, h1396, h1574, h1582, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1584 | h1584
                  · linarith only [h1395, h1396, h1584, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1586 | h1586
                    · linarith only [h1396, h1586, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1586, hc01, hlam, hphi, ht12, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1589 | h1589
            · linarith only [h1395, h1589, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1591 | h1591
              · linarith only [h1394, h1395, h1591, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1593 | h1593
                · linarith only [h1394, h1395, h1593, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1595 | h1595
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1596 | h1596
                    · linarith only [h1589, h1596, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1596, hc01, hlam, hphi, ht12, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1599 | h1599
                    · linarith only [h1394, h1589, h1599, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1599, hc01, hlam, hphi, ht12, u2elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1602 | h1602
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1603 | h1603
            · linarith only [h1394, h1603, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1605 | h1605
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1606 | h1606
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1607 | h1607
                  · linarith only [h1394, h1602, h1607, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1609 | h1609
                    · linarith only [h1603, h1609, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1609, hc01, hlam, hphi, ht12, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1612 | h1612
                  · linarith only [h1394, h1602, h1612, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1614 | h1614
                    · linarith only [h1602, h1603, h1614, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1614, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1394, h1602, h1605, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1618 | h1618
            · linarith only [h1602, h1618, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1620 | h1620
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1621 | h1621
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1622 | h1622
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1623 | h1623
                    · linarith only [h1618, h1623, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1623, hc01, hlam, hphi, ht12, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1626 | h1626
                    · linarith only [h0, h1618, h1626, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1626, hc01, hlam, hphi, ht12, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1629 | h1629
                  · linarith only [h1620, h1621, h1629, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1631 | h1631
                    · linarith only [h0, h1618, h1631, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1631, hc01, hlam, hphi, ht12, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1634 | h1634
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1635 | h1635
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1636 | h1636
                    · linarith only [h0, h1618, h1636, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1636, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1620, h1634, h1635, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1640 | h1640
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1641 | h1641
                    · linarith only [h0, h1618, h1641, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1641, hc01, hlam, hphi, ht12, u2elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1644 | h1644
                    · linarith only [h0, h1618, h1644, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1644, hc01, hlam, hphi, ht12, u2elo4]

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
