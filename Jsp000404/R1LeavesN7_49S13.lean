import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1113 | h1113
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1114 | h1114
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1116 | h1116
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1117 | h1117
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1118 | h1118
            · linarith only [h1118, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1121 | h1121
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1122 | h1122
                  · linarith only [h1113, h1120, h1122, h2, h6, hc12, hlam, hphi, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1124 | h1124
                    · linarith only [h1124, h2, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h1bigk with h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1113, h1121, h1124, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1126_1]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        rcases p1126_3 (m.d 0 1) (by simp) with h1129 | h1129
                        · rcases p1126_3 (m.d 1 2) (by simp) with h1130 | h1130
                          · linarith only [h0, h1130, hlam]
                          · linarith only [h1113, h1130, hlam]
                        · linarith only [h1129, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        rcases p1126_3 (m.d 0 1) (by simp) with h1134 | h1134
                        · rcases p1126_3 (m.d 1 2) (by simp) with h1135 | h1135
                          · linarith only [h0, h1135, hlam]
                          · linarith only [h1114, h1135, hlam]
                        · linarith only [h1134, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        rcases p1126_3 (m.d 0 1) (by simp) with h1139 | h1139
                        · rcases p1126_3 (m.d 1 2) (by simp) with h1140 | h1140
                          · linarith only [h0, h1140, hlam]
                          · linarith only [h1115, h1140, hlam]
                        · linarith only [h1139, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h0, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1117, h1118, hc12, hlam, hphi, p1126_1, u1ehi3]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1126_1, u1ehi3]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h0, h1118, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1126_1, u1ehi3]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1113, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hc13, hlam, hphi, p1126_1, u1ehi3]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h0, h1113, h1118, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1126_1, u1ehi3]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h2, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1114, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1116, hlam, p1126_1]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1118, hlam, p1126_1]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h3, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1115, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [h1117, hlam, p1126_0]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hc15, hlam, hphi, p1126_1, u1ehi3]
                      · have p1126_0 := h1126c.1
                        have p1126_1 := h1126c.2.1
                        have p1126_2 := h1126c.2.2.1
                        have p1126_3 := h1126c.2.2.2
                        linarith only [hlam, p1126_0]
                · linarith only [h0, h1113, h1117, h1120, h1121, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1165 | h1165
                · linarith only [h0, h1113, h1116, h1120, h1165, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1167 | h1167
                  · linarith only [h1167, h2, h6, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1169 | h1169
                    · linarith only [h1116, h1169, h2, h6, hlam]
                    · rcases h1bigk with h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1113, h1117, h1120, h1169, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1171_1]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1117, h1120, h1169, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1171_1]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        rcases p1171_3 (m.d 0 1) (by simp) with h1175 | h1175
                        · rcases p1171_3 (m.d 1 2) (by simp) with h1176 | h1176
                          · linarith only [h0, h1176, hlam]
                          · linarith only [h1114, h1176, hlam]
                        · linarith only [h1175, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        rcases p1171_3 (m.d 0 1) (by simp) with h1180 | h1180
                        · rcases p1171_3 (m.d 1 2) (by simp) with h1181 | h1181
                          · linarith only [h0, h1181, hlam]
                          · linarith only [h1115, h1181, hlam]
                        · linarith only [h1180, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h0, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1117, h1120, h1169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1171_1]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1171_1, u1ehi3]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h0, h1118, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1171_1, u1ehi3]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1113, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hc13, hlam, hphi, p1171_1, u1ehi3]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h0, h1113, h1118, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1171_1, u1ehi3]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h2, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1114, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1116, hlam, p1171_1]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1118, hlam, p1171_1]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h3, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1115, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [h1117, hlam, p1171_0]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hc15, hlam, hphi, p1171_1, u1ehi3]
                      · have p1171_0 := h1171c.1
                        have p1171_1 := h1171c.2.1
                        have p1171_2 := h1171c.2.2.1
                        have p1171_3 := h1171c.2.2.2
                        linarith only [hlam, p1171_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1205 | h1205
            · linarith only [h1205, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1207 | h1207
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1208 | h1208
                · linarith only [h0, h1113, h1117, h1208, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1210 | h1210
                  · linarith only [h1210, h2, h6, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1212 | h1212
                    · linarith only [h1113, h1117, h1207, h1212, h2, h3, h6, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h1bigk with h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1113, h1207, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1214_1]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        rcases p1214_3 (m.d 0 1) (by simp) with h1217 | h1217
                        · rcases p1214_3 (m.d 1 2) (by simp) with h1218 | h1218
                          · linarith only [h0, h1218, hlam]
                          · linarith only [h1113, h1218, hlam]
                        · linarith only [h1217, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        rcases p1214_3 (m.d 0 1) (by simp) with h1222 | h1222
                        · rcases p1214_3 (m.d 1 2) (by simp) with h1223 | h1223
                          · linarith only [h0, h1223, hlam]
                          · linarith only [h1114, h1223, hlam]
                        · linarith only [h1222, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        rcases p1214_3 (m.d 0 1) (by simp) with h1227 | h1227
                        · rcases p1214_3 (m.d 1 2) (by simp) with h1228 | h1228
                          · linarith only [h0, h1228, hlam]
                          · linarith only [h1115, h1228, hlam]
                        · linarith only [h1227, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h0, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1116, hc12, hlam, hphi, p1214_1, u1ehi3]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1214_1, u1ehi3]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1214_1, u1ehi4]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1113, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hc13, hlam, hphi, p1214_1, u1ehi3]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1117, hlam, p1214_1]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h2, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1114, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1116, hlam, p1214_1]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1205, hlam, p1214_1]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h3, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h1115, hlam, p1214_0]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hc15, hlam, hphi, p1214_1, u1ehi2]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [h0, h1115, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1214_1, u1ehi3]
                      · have p1214_0 := h1214c.1
                        have p1214_1 := h1214c.2.1
                        have p1214_2 := h1214c.2.2.1
                        have p1214_3 := h1214c.2.2.2
                        linarith only [hlam, p1214_0]
              · linarith only [h1116, h1117, h1207, hc23, hc35, hlam, hphi]
        · linarith only [h1116, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1254 | h1254
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1255 | h1255
          · linarith only [h1113, h1115, h1255, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1257 | h1257
            · linarith only [h1257, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1259 | h1259
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1260 | h1260
                · linarith only [h1113, h1115, h1254, h1255, h1260, hc25, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1262 | h1262
                  · linarith only [h1262, h4, h6, hlam]
                  · linarith only [h1113, h1115, h1259, h1262, hc34, hc45, hlam, hphi]
              · linarith only [h1254, h1255, h1259, hc23, hc35, hlam, hphi]
        · linarith only [h1254, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · linarith only [h1114, h4, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1268 | h1268
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1269 | h1269
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1270 | h1270
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1271 | h1271
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1272 | h1272
            · linarith only [h1272, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1274 | h1274
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1275 | h1275
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1276 | h1276
                  · linarith only [h1113, h1268, h1276, h2, h6, hc23, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1278 | h1278
                    · linarith only [h1113, h1269, h1274, h1276, h1278, h2, h6, hc23, hlam, hphi, ht12, u1ehi3]
                    · rcases h1bigk with h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        rcases p1280_3 (m.d 0 1) (by simp) with h1282 | h1282
                        · rcases p1280_3 (m.d 1 2) (by simp) with h1283 | h1283
                          · linarith only [h1283, hlam, p1280_0]
                          · rcases p1280_3 (m.d 1 3) (by simp) with h1285 | h1285
                            · linarith only [h1, h1285, hlam]
                            · linarith only [h1113, h1285, hlam]
                        · linarith only [h1282, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        rcases p1280_3 (m.d 0 1) (by simp) with h1289 | h1289
                        · rcases p1280_3 (m.d 1 2) (by simp) with h1290 | h1290
                          · linarith only [h0, h1290, hlam]
                          · rcases p1280_3 (m.d 1 3) (by simp) with h1292 | h1292
                            · linarith only [h1292, hlam, p1280_0]
                            · rcases p1280_3 (m.d 1 4) (by simp) with h1294 | h1294
                              · linarith only [h1294, h2, hlam]
                              · rcases p1280_3 (m.d 1 5) (by simp) with h1296 | h1296
                                · linarith only [h1296, h3, hlam]
                                · rcases h4bigk with h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, p1298_1, u1ehi3]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h6, hc24, hc45, hlam, hphi, p1298_1]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h6, hc34, hc45, hlam, hphi, p1298_1]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h6, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h2, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1274, h2, h6, hc34, hc45, hlam, hphi, p1298_1]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1113, h1269, h1272, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1280_1, p1298_1]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1272, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h4, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1268, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h4, h6, hc34, hc45, hlam, hphi, p1298_1]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1276, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h5, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1270, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1274, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h1278, hlam, p1298_0]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p1298_1, u1ehi3]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p1298_1, u1ehi3]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    rcases p1298_3 (m.d 0 4) (by simp) with h1321 | h1321
                                    · linarith only [h1321, h6, hlam]
                                    · linarith only [h1321, h4, hlam]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    rcases p1298_3 (m.d 0 4) (by simp) with h1324 | h1324
                                    · linarith only [h1324, h6, hlam]
                                    · linarith only [h1324, h5, hlam]
                                  · have p1298_0 := h1298c.1
                                    have p1298_1 := h1298c.2.1
                                    have p1298_2 := h1298c.2.2.1
                                    have p1298_3 := h1298c.2.2.2
                                    linarith only [hlam, p1298_0]
                        · linarith only [h1289, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        rcases p1280_3 (m.d 0 1) (by simp) with h1329 | h1329
                        · rcases p1280_3 (m.d 1 2) (by simp) with h1330 | h1330
                          · linarith only [h0, h1330, hlam]
                          · linarith only [h1268, h1330, hlam]
                        · linarith only [h1329, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        rcases p1280_3 (m.d 0 1) (by simp) with h1334 | h1334
                        · rcases p1280_3 (m.d 1 2) (by simp) with h1335 | h1335
                          · linarith only [h0, h1335, hlam]
                          · linarith only [h1269, h1335, hlam]
                        · linarith only [h1334, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h0, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1113, hlam, p1280_1]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hc12, hlam, hphi, p1280_1, u1ehi3]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1113, hc23, hlam, hphi, ht12, p1280_1, u1ehi4]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1, h1269, h1276, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1280_1]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1280_1, u1ehi3]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1280_1, u1ehi4]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h2, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1268, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1270, hlam, p1280_1]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1272, hlam, p1280_1]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h3, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1269, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [h1271, hlam, p1280_0]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hc15, hlam, hphi, p1280_1, u1ehi3]
                      · have p1280_0 := h1280c.1
                        have p1280_1 := h1280c.2.1
                        have p1280_2 := h1280c.2.2.1
                        have p1280_3 := h1280c.2.2.2
                        linarith only [hlam, p1280_0]
                · linarith only [h1113, h1275, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1113, h1269, h1272, h1274, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · linarith only [h1113, h1269, h1271, hlam]
        · linarith only [h1113, h1270, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1364 | h1364
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1365 | h1365
            · linarith only [h1365, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1367 | h1367
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1368 | h1368
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1369 | h1369
                  · linarith only [h1268, h1269, h1368, h1369, h2, h6, hc23, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1371 | h1371
                    · linarith only [h1268, h1269, h1367, h1369, h1371, hlam]
                    · rcases h1bigk with h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        rcases p1373_3 (m.d 0 1) (by simp) with h1375 | h1375
                        · rcases p1373_3 (m.d 1 2) (by simp) with h1376 | h1376
                          · linarith only [h1376, hlam, p1373_0]
                          · rcases p1373_3 (m.d 1 3) (by simp) with h1378 | h1378
                            · linarith only [h1, h1378, hlam]
                            · linarith only [h1113, h1378, hlam]
                        · linarith only [h1375, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        rcases p1373_3 (m.d 0 1) (by simp) with h1382 | h1382
                        · rcases p1373_3 (m.d 1 2) (by simp) with h1383 | h1383
                          · linarith only [h0, h1383, hlam]
                          · rcases p1373_3 (m.d 1 3) (by simp) with h1385 | h1385
                            · linarith only [h1385, hlam, p1373_0]
                            · rcases p1373_3 (m.d 1 4) (by simp) with h1387 | h1387
                              · linarith only [h1387, h2, hlam]
                              · rcases p1373_3 (m.d 1 5) (by simp) with h1389 | h1389
                                · linarith only [h1389, h3, hlam]
                                · rcases h4bigk with h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, p1391_1, u1ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h6, hc24, hc45, hlam, hphi, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h6, hc34, hc45, hlam, hphi, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h6, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h2, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1367, h2, h6, hc34, hc45, hlam, hphi, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1268, h1269, h1364, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1373_1, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1365, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h4, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1268, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h4, h6, hc34, hc45, hlam, hphi, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1369, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h5, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1363, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1367, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1371, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p1391_1, u1ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p1391_1, u1ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    rcases p1391_3 (m.d 0 4) (by simp) with h1414 | h1414
                                    · linarith only [h1414, h6, hlam]
                                    · linarith only [h1414, h4, hlam]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    rcases p1391_3 (m.d 0 4) (by simp) with h1417 | h1417
                                    · linarith only [h1417, h6, hlam]
                                    · linarith only [h1417, h5, hlam]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                        · linarith only [h1382, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        rcases p1373_3 (m.d 0 1) (by simp) with h1422 | h1422
                        · rcases p1373_3 (m.d 1 2) (by simp) with h1423 | h1423
                          · linarith only [h0, h1423, hlam]
                          · linarith only [h1268, h1423, hlam]
                        · linarith only [h1422, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        rcases p1373_3 (m.d 0 1) (by simp) with h1427 | h1427
                        · rcases p1373_3 (m.d 1 2) (by simp) with h1428 | h1428
                          · linarith only [h0, h1428, hlam]
                          · rcases p1373_3 (m.d 1 3) (by simp) with h1430 | h1430
                            · linarith only [h1, h1430, hlam]
                            · linarith only [h1364, h1430, hlam]
                        · linarith only [h1427, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h0, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1113, hlam, p1373_1]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [hc12, hlam, hphi, p1373_1, u1ehi3]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1269, hlam, p1373_1]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1, h1268, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1373_1]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1373_1, u1ehi3]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1373_1, u1ehi4]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h2, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1268, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1363, hlam, p1373_1]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1365, hlam, p1373_1]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h3, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1268, hc15, hlam, hphi, p1373_1, u1ehi3]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1364, hlam, p1373_0]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [h1, h1364, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1373_1, u1ehi3]
                      · have p1373_0 := h1373c.1
                        have p1373_1 := h1373c.2.1
                        have p1373_2 := h1373c.2.2.1
                        have p1373_3 := h1373c.2.2.2
                        linarith only [hlam, p1373_0]
                · linarith only [h1, h1113, h1268, h1364, h1368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
              · linarith only [h1113, h1367, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1456 | h1456
            · linarith only [h1456, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1458 | h1458
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1459 | h1459
                · linarith only [h1113, h1364, h1459, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h1113, h1268, h1459, hc35, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h1113, h1268, h1458, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h1113, h1268, h1363, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
    · linarith only [h1268, h4, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1465 | h1465
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1466 | h1466
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1467 | h1467
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1468 | h1468
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1469 | h1469
          · linarith only [h1, h1469, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1471 | h1471
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1472 | h1472
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1473 | h1473
                · linarith only [h1, h1466, h1473, h5, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1475 | h1475
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1476 | h1476
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1477 | h1477
                      · rcases h1bigk with h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c | h1478c
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1466, h1475, h1477, hc01, hc45, hlam, hphi, ht0b, ht5b, p1478_1]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          rcases p1478_3 (m.d 0 1) (by simp) with h1481 | h1481
                          · rcases p1478_3 (m.d 1 2) (by simp) with h1482 | h1482
                            · linarith only [h0, h1482, hlam]
                            · linarith only [h1466, h1482, hlam]
                          · linarith only [h1481, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          rcases p1478_3 (m.d 0 1) (by simp) with h1486 | h1486
                          · rcases p1478_3 (m.d 1 2) (by simp) with h1487 | h1487
                            · linarith only [h0, h1487, hlam]
                            · linarith only [h1467, h1487, hlam]
                          · linarith only [h1486, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          rcases p1478_3 (m.d 0 1) (by simp) with h1491 | h1491
                          · rcases p1478_3 (m.d 1 2) (by simp) with h1492 | h1492
                            · linarith only [h0, h1492, hlam]
                            · linarith only [h1468, h1492, hlam]
                          · linarith only [h1491, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h0, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1471, hc12, hlam, hphi, p1478_1, u1ehi4]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1478_1, u1ehi3]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1478_1, u1ehi4]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1466, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1469, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hc13, hlam, hphi, p1478_1, u1ehi4]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h2, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1467, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hc14, hlam, hphi, p1478_1, u1ehi2]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h0, h1467, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1478_1, u1ehi4]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h3, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1468, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1471, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [h1472, hlam, p1478_0]
                        · have p1478_0 := h1478c.1
                          have p1478_1 := h1478c.2.1
                          have p1478_2 := h1478c.2.2.1
                          have p1478_3 := h1478c.2.2.2
                          linarith only [hlam, p1478_0]
                      · linarith only [h1, h1471, h1477, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                    · linarith only [h0, h1467, h1472, h1473, h1475, h1476, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h1471, h1475, h5, hc23, hc34, hlam, hphi]
              · linarith only [h1465, h1472, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1520 | h1520
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1521 | h1521
                · linarith only [h1, h1521, h5, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1523 | h1523
                  · linarith only [h1471, h1523, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1525 | h1525
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1526 | h1526
                      · rcases h1bigk with h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1467, h1525, hc01, hc45, hlam, hphi, ht0b, ht5b, p1527_1]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          rcases p1527_3 (m.d 0 1) (by simp) with h1530 | h1530
                          · rcases p1527_3 (m.d 1 2) (by simp) with h1531 | h1531
                            · linarith only [h0, h1531, hlam]
                            · linarith only [h1466, h1531, hlam]
                          · linarith only [h1530, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          rcases p1527_3 (m.d 0 1) (by simp) with h1535 | h1535
                          · rcases p1527_3 (m.d 1 2) (by simp) with h1536 | h1536
                            · linarith only [h0, h1536, hlam]
                            · linarith only [h1467, h1536, hlam]
                          · linarith only [h1535, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          rcases p1527_3 (m.d 0 1) (by simp) with h1540 | h1540
                          · rcases p1527_3 (m.d 1 2) (by simp) with h1541 | h1541
                            · linarith only [h0, h1541, hlam]
                            · linarith only [h1468, h1541, hlam]
                          · linarith only [h1540, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h0, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hc12, hlam, hphi, p1527_1, u1ehi2]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h0, h1471, h1520, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1527_1, u1ehi2]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h0, h1471, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1527_1, u1ehi2]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1466, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1469, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1471, hlam, p1527_1]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h2, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1467, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hc14, hlam, hphi, p1527_1, u1ehi2]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h0, h1467, h1471, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1527_1, u1ehi2]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h3, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1468, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hc15, hlam, hphi, p1527_1, u1ehi2]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [h1520, hlam, p1527_0]
                        · have p1527_0 := h1527c.1
                          have p1527_1 := h1527c.2.1
                          have p1527_2 := h1527c.2.2.1
                          have p1527_3 := h1527c.2.2.2
                          linarith only [hlam, p1527_0]
                      · linarith only [h1, h1525, h1526, h5, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1566 | h1566
                      · rcases h1bigk with h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1467, h1520, h1521, h1525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1567_1]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          rcases p1567_3 (m.d 0 1) (by simp) with h1570 | h1570
                          · rcases p1567_3 (m.d 1 2) (by simp) with h1571 | h1571
                            · linarith only [h0, h1571, hlam]
                            · linarith only [h1466, h1571, hlam]
                          · linarith only [h1570, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1520, h1521, h1525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1567_1]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          rcases p1567_3 (m.d 0 1) (by simp) with h1576 | h1576
                          · rcases p1567_3 (m.d 1 2) (by simp) with h1577 | h1577
                            · linarith only [h0, h1577, hlam]
                            · linarith only [h1468, h1577, hlam]
                          · linarith only [h1576, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h0, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hc12, hlam, hphi, p1567_1, u1ehi2]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h0, h1520, h1521, h1525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1567_1]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1567_1, u1ehi4]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1466, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1469, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1471, hlam, p1567_1]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h2, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1467, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hc14, hlam, hphi, p1567_1, u1ehi2]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h0, h1467, h1471, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1567_1, u1ehi2]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h3, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1468, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hc15, hlam, hphi, p1567_1, u1ehi2]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [h1520, hlam, p1567_0]
                        · have p1567_0 := h1567c.1
                          have p1567_1 := h1567c.2.1
                          have p1567_2 := h1567c.2.2.1
                          have p1567_3 := h1567c.2.2.2
                          linarith only [hlam, p1567_0]
                      · linarith only [h1, h1566, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h1465, h1520, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1603 | h1603
          · linarith only [h1, h1603, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1605 | h1605
            · linarith only [h1467, h1468, h1603, h1605, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1607 | h1607
              · linarith only [h1467, h1468, h1607, hlam]
              · linarith only [h1465, h1603, h1607, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1610 | h1610
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1611 | h1611
          · linarith only [h1, h1467, h1611, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1613 | h1613
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1614 | h1614
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1615 | h1615
                · linarith only [h1466, h1467, h1613, h1615, h4, h5, hc23, hlam, hphi, ht12, u1ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1617 | h1617
                  · linarith only [h0, h1466, h1467, h1617, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1466, h1467, h1613, h1617, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h1465, h1466, h1467, h1613, h1614, h5, hc34, hlam, hphi, ht12, ht23, u1ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1621 | h1621
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1622 | h1622
                · linarith only [h1467, h1622, h4, h5, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1624 | h1624
                  · linarith only [h0, h1466, h1467, h1613, h1624, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1626 | h1626
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1627 | h1627
                      · rcases h1bigk with h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          rcases p1628_3 (m.d 0 1) (by simp) with h1630 | h1630
                          · rcases p1628_3 (m.d 1 2) (by simp) with h1631 | h1631
                            · linarith only [h1631, hlam, p1628_0]
                            · rcases p1628_3 (m.d 1 3) (by simp) with h1633 | h1633
                              · linarith only [h1, h1633, hlam]
                              · rcases p1628_3 (m.d 1 4) (by simp) with h1635 | h1635
                                · linarith only [h1635, h2, hlam]
                                · linarith only [h1467, h1635, hlam]
                          · linarith only [h1630, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          rcases p1628_3 (m.d 0 1) (by simp) with h1639 | h1639
                          · rcases p1628_3 (m.d 1 2) (by simp) with h1640 | h1640
                            · linarith only [h0, h1640, hlam]
                            · linarith only [h1466, h1640, hlam]
                          · linarith only [h1639, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          rcases p1628_3 (m.d 0 1) (by simp) with h1644 | h1644
                          · rcases p1628_3 (m.d 1 2) (by simp) with h1645 | h1645
                            · linarith only [h0, h1645, hlam]
                            · rcases p1628_3 (m.d 1 3) (by simp) with h1647 | h1647
                              · linarith only [h1, h1647, hlam]
                              · rcases p1628_3 (m.d 1 4) (by simp) with h1649 | h1649
                                · linarith only [h1649, hlam, p1628_0]
                                · rcases p1628_3 (m.d 1 5) (by simp) with h1651 | h1651
                                  · linarith only [h1651, h3, hlam]
                                  · rcases h4bigk with h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1467, h1610, h1624, h5, hc23, hc34, hlam, hphi, p1653_1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1467, h1610, h5, hc34, hlam, hphi, ht12, ht23, p1653_1, u1ehi4]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h5, hlam, p1653_1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      rcases p1653_3 (m.d 0 4) (by simp) with h1658 | h1658
                                      · rcases p1653_3 (m.d 1 4) (by simp) with h1659 | h1659
                                        · linarith only [h1659, h2, hlam]
                                        · linarith only [h1621, h1659, hlam]
                                      · linarith only [h1658, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h2, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1467, hlam, p1653_1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1611, hlam, p1653_1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p1628_1, p1653_1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h4, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1653_1, u1ehi3]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1622, hlam, p1653_1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      rcases p1653_3 (m.d 0 4) (by simp) with h1672 | h1672
                                      · rcases p1653_3 (m.d 1 4) (by simp) with h1673 | h1673
                                        · linarith only [h1467, h1673, hlam]
                                        · linarith only [h1621, h1673, hlam]
                                      · linarith only [h1465, h1672, hlam]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1467, h2, hc34, hlam, hphi, ht12, ht23, p1653_1, u1ehi1]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1467, h1610, hc34, hlam, hphi, ht12, ht23, p1653_1, u1ehi4]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1467, h1610, h1613, hc34, hlam, hphi, ht12, ht23, p1653_1, u1ehi2]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      rcases p1653_3 (m.d 0 4) (by simp) with h1681 | h1681
                                      · linarith only [h1681, h5, hlam]
                                      · linarith only [h1465, h1681, hlam]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1465, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1621, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1626, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [h1627, hlam, p1653_0]
                                    · have p1653_0 := h1653c.1
                                      have p1653_1 := h1653c.2.1
                                      have p1653_2 := h1653c.2.2.1
                                      have p1653_3 := h1653c.2.2.2
                                      linarith only [hlam, p1653_0]
                          · linarith only [h1644, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          rcases p1628_3 (m.d 0 1) (by simp) with h1690 | h1690
                          · rcases p1628_3 (m.d 1 2) (by simp) with h1691 | h1691
                            · linarith only [h0, h1691, hlam]
                            · linarith only [h1610, h1691, hlam]
                          · linarith only [h1690, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h0, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1467, h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1628_1, u1ehi2]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1467, hlam, p1628_1]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h0, h1467, h1613, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1628_1, u1ehi2]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1466, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1611, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1613, hlam, p1628_1]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h2, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [hc14, hlam, hphi, p1628_1, u1ehi1]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h0, h1467, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1628_1, u1ehi2]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h0, h1467, h1613, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1628_1, u1ehi2]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h3, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1610, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1610, hc12, hlam, hphi, p1628_1, u1ehi2]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [h1621, hlam, p1628_0]
                        · have p1628_0 := h1628c.1
                          have p1628_1 := h1628c.2.1
                          have p1628_2 := h1628c.2.2.1
                          have p1628_3 := h1628c.2.2.2
                          linarith only [hlam, p1628_0]
                      · linarith only [h1467, h1627, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1467, h1610, h1621, h1626, hlam]
              · linarith only [h1465, h1621, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1718 | h1718
          · linarith only [h1467, h1718, h4, h5, hc13, hlam, hphi, u1ehi1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1720 | h1720
            · linarith only [h1466, h1610, h1720, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1722 | h1722
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1723 | h1723
                · linarith only [h1, h1723, h5, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                  · linarith only [h1466, h1467, h1720, h1725, h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1727 | h1727
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1728 | h1728
                      · rcases h1bigk with h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          rcases p1729_3 (m.d 0 1) (by simp) with h1731 | h1731
                          · rcases p1729_3 (m.d 1 2) (by simp) with h1732 | h1732
                            · linarith only [h1732, hlam, p1729_0]
                            · rcases p1729_3 (m.d 1 3) (by simp) with h1734 | h1734
                              · linarith only [h1, h1734, hlam]
                              · rcases p1729_3 (m.d 1 4) (by simp) with h1736 | h1736
                                · linarith only [h1736, h2, hlam]
                                · linarith only [h1467, h1736, hlam]
                          · linarith only [h1731, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          rcases p1729_3 (m.d 0 1) (by simp) with h1740 | h1740
                          · rcases p1729_3 (m.d 1 2) (by simp) with h1741 | h1741
                            · linarith only [h0, h1741, hlam]
                            · linarith only [h1466, h1741, hlam]
                          · linarith only [h1740, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          rcases p1729_3 (m.d 0 1) (by simp) with h1745 | h1745
                          · rcases p1729_3 (m.d 1 2) (by simp) with h1746 | h1746
                            · linarith only [h0, h1746, hlam]
                            · rcases p1729_3 (m.d 1 3) (by simp) with h1748 | h1748
                              · linarith only [h1, h1748, hlam]
                              · rcases p1729_3 (m.d 1 4) (by simp) with h1750 | h1750
                                · linarith only [h1750, hlam, p1729_0]
                                · rcases p1729_3 (m.d 1 5) (by simp) with h1752 | h1752
                                  · linarith only [h1752, h3, hlam]
                                  · rcases h4bigk with h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1466, h1610, h1722, h5, hc23, hc34, hlam, hphi, p1754_1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1610, h1727, h5, hc34, hlam, hphi, ht12, ht23, p1754_1, u1ehi1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h5, hlam, p1754_1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      rcases p1754_3 (m.d 0 4) (by simp) with h1759 | h1759
                                      · rcases p1754_3 (m.d 1 4) (by simp) with h1760 | h1760
                                        · linarith only [h1760, h2, hlam]
                                        · linarith only [h1722, h1760, hlam]
                                      · linarith only [h1759, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h2, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1467, hlam, p1754_1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1718, hlam, p1754_1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p1729_1, p1754_1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h4, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1754_1, u1ehi3]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1723, hlam, p1754_1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      rcases p1754_3 (m.d 0 4) (by simp) with h1773 | h1773
                                      · rcases p1754_3 (m.d 1 4) (by simp) with h1774 | h1774
                                        · linarith only [h1467, h1774, hlam]
                                        · linarith only [h1722, h1774, hlam]
                                      · linarith only [h1465, h1773, hlam]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1610, h1722, h2, hc34, hlam, hphi, ht12, ht23, p1754_1, u1ehi1]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1466, h1610, h1722, hc34, hlam, hphi, ht12, ht23, p1754_1, u1ehi2]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1466, h1467, hc34, hlam, hphi, ht12, ht23, p1754_1, u1ehi2]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      rcases p1754_3 (m.d 0 4) (by simp) with h1782 | h1782
                                      · linarith only [h1782, h5, hlam]
                                      · linarith only [h1465, h1782, hlam]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1465, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1722, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1727, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [h1728, hlam, p1754_0]
                                    · have p1754_0 := h1754c.1
                                      have p1754_1 := h1754c.2.1
                                      have p1754_2 := h1754c.2.2.1
                                      have p1754_3 := h1754c.2.2.2
                                      linarith only [hlam, p1754_0]
                          · linarith only [h1745, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          rcases p1729_3 (m.d 0 1) (by simp) with h1791 | h1791
                          · rcases p1729_3 (m.d 1 2) (by simp) with h1792 | h1792
                            · linarith only [h0, h1792, hlam]
                            · rcases p1729_3 (m.d 1 3) (by simp) with h1794 | h1794
                              · linarith only [h1, h1794, hlam]
                              · rcases p1729_3 (m.d 1 4) (by simp) with h1796 | h1796
                                · linarith only [h1796, h2, hlam]
                                · linarith only [h1722, h1796, hlam]
                          · linarith only [h1791, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h0, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1610, h1727, h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1729_1, u1ehi2]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1467, hlam, p1729_1]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1610, hlam, p1729_1]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1466, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1718, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1720, hlam, p1729_1]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h2, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hc14, hlam, hphi, p1729_1, u1ehi1]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h0, h1467, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1729_1, u1ehi2]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h0, h1467, h1610, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1729_1, u1ehi1]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h3, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hc15, hlam, hphi, p1729_1, u1ehi1]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h0, h1610, h1727, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1729_1, u1ehi2]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [h1722, hlam, p1729_0]
                        · have p1729_0 := h1729c.1
                          have p1729_1 := h1729c.2.1
                          have p1729_2 := h1729c.2.2.1
                          have p1729_3 := h1729c.2.2.2
                          linarith only [hlam, p1729_0]
                      · linarith only [h1, h1728, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h1467, h1722, h1727, hlam]
              · linarith only [h1465, h1722, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1823 | h1823
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1824 | h1824
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1825 | h1825
          · linarith only [h1, h1825, h5, hlam]
          · linarith only [h1466, h1823, h1825, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1828 | h1828
          · linarith only [h1, h1828, h5, hlam]
          · linarith only [h1466, h1823, h1828, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1831 | h1831
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1832 | h1832
          · linarith only [h1, h1832, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1834 | h1834
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1835 | h1835
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1836 | h1836
                · linarith only [h1, h1466, h1831, h1836, h5, hc23, hlam, hphi, ht12, u1ehi4]
                · linarith only [h1466, h1831, h1836, hc34, hlam, hphi, ht12, ht23, u1ehi4]
              · linarith only [h1465, h1466, h1831, h1832, h1835, h5, hc34, hlam, hphi, ht12, ht23, u1ehi4]
            · linarith only [h1466, h1831, h1834, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1841 | h1841
          · linarith only [h1, h1841, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1843 | h1843
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1844 | h1844
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1845 | h1845
                · linarith only [h1, h1831, h1843, h1845, h5, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h1466, h1845, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1465, h1831, h1841, h1843, h1844, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1849 | h1849
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1850 | h1850
                · linarith only [h1, h1850, h5, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h1466, h1850, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1465, h1849, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1854 | h1854
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1855 | h1855
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1856 | h1856
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1857 | h1857
          · linarith only [h1, h1857, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1859 | h1859
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1860 | h1860
              · linarith only [h1465, h1860, h2, hlam]
              · linarith only [h1857, h1859, h1860, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1863 | h1863
              · linarith only [h1, h1465, h1863, h5, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1865 | h1865
                · linarith only [h1, h1854, h1865, h5, hc12, hlam, hphi, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1867 | h1867
                  · linarith only [h1859, h1867, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1869 | h1869
                    · linarith only [h1, h1465, h1855, h1869, h5, hc14, hlam, hphi, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1871 | h1871
                      · linarith only [h1465, h1871, h2, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h1, h1871, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1874 | h1874
          · linarith only [h1, h1874, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1876 | h1876
            · linarith only [h1854, h1856, h1876, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1878 | h1878
              · linarith only [h1, h1465, h1855, h1878, h5, hc12, hlam, hphi, u1ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1880 | h1880
                · linarith only [h1, h1854, h1856, h1880, h5, hc25, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1882 | h1882
                  · linarith only [h1465, h1876, h1880, h1882, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1884 | h1884
                    · linarith only [h1465, h1855, h1856, h1882, h1884, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1886 | h1886
                      · linarith only [h1855, h1856, h1880, h1884, h1886, hc23, hc34, hlam, hphi]
                      · linarith only [h1, h1886, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · linarith only [h1465, h1855, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1890 | h1890
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1891 | h1891
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1892 | h1892
          · linarith only [h1, h1892, h5, hlam]
          · linarith only [h1854, h1890, h1892, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1895 | h1895
          · linarith only [h1, h1895, h5, hlam]
          · linarith only [h1854, h1890, h1895, hlam]
      · linarith only [h1465, h1890, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3 h4 h5
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3 h4 h5

end R2N4
