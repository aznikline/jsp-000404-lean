import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3626000 in
set_option maxHeartbeats 3626000 in
theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h720 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h970 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1097 | h1097
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1098 | h1098
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1099 | h1099
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1101 | h1101
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1102 | h1102
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1103 | h1103
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1105 | h1105
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1106 | h1106
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1107 | h1107
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1108 | h1108
                        · rcases h0bigk with h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1097, h1105, h1108, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi4]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h720, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h970, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, h1097, h1105, h1108, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi4]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, h970, hc01, hc12, hlam, hphi, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, h1097, hc01, hc12, hlam, hphi, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1097, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, h1097, h1098, h1100, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1109_1, u2ehi4]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h0, h1097, h1098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1109_1, u2ehi4]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1101, h720, hc01, hc12, hlam, hphi, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1101, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1109_1, u2ehi0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1101, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1109_1, u3ehi0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1098, h1101, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1109_1, u2ehi4]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1101, h1104, h970, hc01, hc12, hlam, hphi, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1098, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1099, hlam, p1109_0]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [h1100, hlam, p1109_1]
                          · have p1109_0 := h1109c.1
                            have p1109_1 := h1109c.2.1
                            have p1109_2 := h1109c.2.2.1
                            have p1109_3 := h1109c.2.2.2
                            linarith only [hlam, p1109_0]
                        · linarith only [h1097, h1105, h1107, h1108, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1136 | h1136
                        · linarith only [h1105, h1107, h1136, hlam]
                        · rcases h0bigk with h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [hlam, p1138_0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, hlam, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1138_1, u3ehi0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h720, hlam, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h970, hlam, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [hlam, p1138_0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1138_1, u3ehi0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, h1100, h1107, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi3]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, h1097, hc01, hc12, hlam, hphi, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1097, hlam, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [hlam, p1138_0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, h1097, h1100, h1107, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi3]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h0, h1097, h1100, h1107, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi3]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1101, h720, hc01, hc12, hlam, hphi, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1101, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1099, h1100, h1101, h1107, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi3]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [hlam, p1138_0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1100, h1101, h1107, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi3]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1101, h1104, h970, hc01, hc12, hlam, hphi, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1098, hlam, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1099, hlam, p1138_0]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [h1100, hlam, p1138_1]
                          · have p1138_0 := h1138c.1
                            have p1138_1 := h1138c.2.1
                            have p1138_2 := h1138c.2.2.1
                            have p1138_3 := h1138c.2.2.2
                            linarith only [hlam, p1138_0]
                    · linarith only [h0, h1097, h1099, h1105, h1106, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1165 | h1165
                    · linarith only [h1105, h1165, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1167 | h1167
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1168 | h1168
                        · rcases h0bigk with h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [hlam, p1169_0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, hlam, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1169_1, u3ehi0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h720, hlam, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h970, hlam, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [hlam, p1169_0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1169_1, u3ehi0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, h1099, h1165, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1169_1, u2ehi2]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, h1097, hc01, hc12, hlam, hphi, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1097, hlam, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [hlam, p1169_0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, h1097, h1099, h1100, h1165, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1169_1, u2ehi2]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h0, h1097, h1099, h1165, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1169_1, u2ehi2]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1101, h720, hc01, hc12, hlam, hphi, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1101, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1169_1, u2ehi0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1099, h1101, h1165, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1169_1, u2ehi2]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [hlam, p1169_0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1099, h1101, h1165, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1169_1, u2ehi2]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1101, h1104, h970, hc01, hc12, hlam, hphi, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1098, hlam, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1099, hlam, p1169_0]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [h1100, hlam, p1169_1]
                          · have p1169_0 := h1169c.1
                            have p1169_1 := h1169c.2.1
                            have p1169_2 := h1169c.2.2.1
                            have p1169_3 := h1169c.2.2.2
                            linarith only [hlam, p1169_0]
                        · linarith only [h1101, h1167, h1168, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1196 | h1196
                        · linarith only [h1103, h1105, h1167, h1196, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1105, h1196, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h1100, h1104, h720, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1200 | h1200
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1201 | h1201
                  · linarith only [h1097, h1103, h1201, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1203 | h1203
                    · linarith only [h1201, h1203, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1206 | h1206
                        · rcases h0bigk with h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1099, h1203, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h720, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h970, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1099, h1203, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, h970, hc01, hc12, hlam, hphi, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, h1097, hc01, hc12, hlam, hphi, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1097, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, h1097, h1099, h1100, h1203, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, h1097, h1099, h1203, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1103, h720, hc01, hc34, hlam, hphi, ht12, ht23, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1097, h1099, h1103, h1203, h720, hc34, hlam, hphi, ht23, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1099, h1103, h1203, h720, hc34, hlam, hphi, ht23, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1099, h1103, h1203, h720, hc34, hlam, hphi, ht23, p1207_1, u2ehi2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h970, hc01, hc15, hlam, hphi, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1098, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1099, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1100, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                        · linarith only [h0, h1097, h1099, h1103, h1203, h1205, h1206, h720, hc01, hc12, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h1100, h1103, h1205, h720, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h1100, h1200, h720, hlam]
            · linarith only [h0, h1097, h1102, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h1097, h1101, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1238 | h1238
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1239 | h1239
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1240 | h1240
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1241 | h1241
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1242 | h1242
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1243 | h1243
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1244 | h1244
                      · linarith only [h0, h1097, h1100, h1242, h1244, h720, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1246 | h1246
                        · linarith only [h1242, h1244, h1246, hlam]
                        · rcases h0bigk with h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hlam, p1248_0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, hlam, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1248_1, u3ehi0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h720, hlam, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h970, hlam, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hlam, p1248_0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1248_1, u3ehi0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, h1098, h1244, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1248_1, u2ehi3]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, h1097, hc01, hc12, hlam, hphi, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h1097, hlam, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hlam, p1248_0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, h1097, h720, hc01, hc12, hlam, hphi, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h0, h1097, h1098, h1244, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1248_1, u2ehi3]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h720, hc01, hc14, hlam, hphi, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1248_1, u2ehi0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1248_1, u3ehi0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hlam, p1248_0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h1100, hlam, p1248_0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h1238, h1241, h970, hc01, hc12, hlam, hphi, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h1098, hlam, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h1099, hlam, p1248_0]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [h1100, h1238, h1241, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1]
                          · have p1248_0 := h1248c.1
                            have p1248_1 := h1248c.2.1
                            have p1248_2 := h1248c.2.2.1
                            have p1248_3 := h1248c.2.2.2
                            linarith only [hlam, p1248_0]
                    · linarith only [h1099, h1100, h1238, h1241, h1242, h1243, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1275 | h1275
                    · linarith only [h1242, h1275, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1277 | h1277
                      · linarith only [h1099, h1100, h1275, h1277, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1279 | h1279
                        · linarith only [h1099, h1100, h1240, h1275, h1279, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1242, h1279, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1282 | h1282
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1283 | h1283
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1284 | h1284
                      · linarith only [h1241, h1284, h720, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1286 | h1286
                        · linarith only [h1241, h1282, h1286, h720, hc01, hc24, hlam, hphi, ht12]
                        · rcases h0bigk with h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [hlam, p1288_0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, hlam, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1288_1, u3ehi0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h720, hlam, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h970, hlam, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [hlam, p1288_0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1288_1, u3ehi0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, h970, hc01, hc12, hlam, hphi, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, h1097, hc01, hc12, hlam, hphi, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1097, hlam, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [hlam, p1288_0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, h1097, h720, hc01, hc12, hlam, hphi, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, h1097, h1098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1288_1, u2ehi4]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1241, h720, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1097, h1283, h1286, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1288_1, u3ehi3]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1241, h720, hc45, hlam, hphi, ht34, p1288_1, u3ehi0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [hlam, p1288_0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1100, hlam, p1288_0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h0, h1097, h1241, h1283, h1286, h970, hc01, hc12, hc45, hlam, hphi, ht34, p1288_1, u3ehi3]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1098, hlam, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1099, hlam, p1288_0]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [h1241, h970, hc04, hc45, hlam, hphi, p1288_1]
                          · have p1288_0 := h1288c.1
                            have p1288_1 := h1288c.2.1
                            have p1288_2 := h1288c.2.2.1
                            have p1288_3 := h1288c.2.2.2
                            linarith only [hlam, p1288_0]
                    · linarith only [h0, h1097, h1099, h1282, h1283, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1240, h1241, h1282, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                  · linarith only [h1100, h1240, h1316, h1317, h720, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1319 | h1319
                    · linarith only [h1317, h1319, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1099, h1100, h1240, h1316, h1319, hc34, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1322 | h1322
                  · linarith only [h0, h1097, h1240, h1322, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1324 | h1324
                    · linarith only [h1238, h1316, h1322, h1324, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1326 | h1326
                      · linarith only [h1238, h1316, h1326, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1328 | h1328
                        · linarith only [h1316, h1328, h720, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1240, h1328, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h0, h1097, h1239, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h1097, h1238, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1333 | h1333
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1334 | h1334
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1335 | h1335
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1337 | h1337
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1338 | h1338
                  · linarith only [h1097, h1099, h1338, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1340 | h1340
                    · linarith only [h1097, h1099, h1340, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1342 | h1342
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1343 | h1343
                        · rcases h0bigk with h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [hlam, p1344_0]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h0, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1097, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1344_1, u2ehi2]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h720, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h970, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [hlam, p1344_0]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h0, h1097, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1344_1, u2ehi2]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h0, h720, hc01, hc12, hlam, hphi, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h0, h970, hc01, hc12, hlam, hphi, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1099, h1343, hc01, hc34, hlam, hphi, ht12, ht23, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1097, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [hlam, p1344_0]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1099, h1336, h1343, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1099, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1334, h720, hc01, hc12, hlam, hphi, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1334, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1344_1, u2ehi0]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1334, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1344_1, u3ehi0]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [hlam, p1344_0]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1097, h1099, h1334, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1344_1, u2ehi2]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1334, h1337, h970, hc01, hc12, hlam, hphi, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1098, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1097, h1099, h1336, h1343, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1344_1, u2ehi2]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [h1333, hlam, p1344_1]
                          · have p1344_0 := h1344c.1
                            have p1344_1 := h1344c.2.1
                            have p1344_2 := h1344c.2.2.1
                            have p1344_3 := h1344c.2.2.2
                            linarith only [hlam, p1344_0]
                        · linarith only [h1338, h1343, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1371 | h1371
                        · linarith only [h1336, h1338, h1342, h1371, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1338, h1371, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h1333, h1337, h720, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1375 | h1375
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1376 | h1376
                  · linarith only [h0, h1097, h1336, h1376, h720, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1378 | h1378
                    · linarith only [h1376, h1378, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1380 | h1380
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1381 | h1381
                        · rcases h0bigk with h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h0, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1382_1, u3ehi0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h720, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h970, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1382_1, u3ehi0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h0, h1333, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h0, h1098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1382_1, u2ehi4]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1099, hc01, hc35, hlam, hphi, ht12, ht23, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1097, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1099, h1333, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1099, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1336, h720, hc01, hc34, hlam, hphi, ht12, ht23, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1336, h720, hc34, hlam, hphi, ht23, p1382_1, u2ehi0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1336, h720, hc34, hlam, hphi, p1382_1, u3ehi0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1097, h1099, h1336, h720, hc34, hlam, hphi, ht23, p1382_1, u2ehi2]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1336, h1375, h970, hc01, hc34, hlam, hphi, ht12, ht23, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1098, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1097, h1336, h1375, h970, hc34, hlam, hphi, ht23, p1382_1, u2ehi2]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1333, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                        · linarith only [h1333, h1336, h1381, h720, hlam]
                      · linarith only [h1333, h1336, h1380, h720, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h1333, h1375, h720, hlam]
            · linarith only [h0, h1098, h1335, hlam]
          · linarith only [h0, h1097, h1334, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1413 | h1413
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1414 | h1414
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1415 | h1415
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1416 | h1416
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1417 | h1417
                  · linarith only [h1097, h1099, h1417, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1419 | h1419
                    · linarith only [h1099, h1415, h1417, h1419, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1421 | h1421
                      · linarith only [h1333, h1413, h1421, h720, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1423 | h1423
                        · linarith only [h1415, h1417, h1421, h1423, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1416, h1417, h1423, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1426 | h1426
                  · linarith only [h1097, h1099, h1426, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1415, h1416, h1426, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1429 | h1429
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1430 | h1430
                  · linarith only [h1097, h1099, h1333, h1415, h1429, h1430, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h1097, h1099, h1333, h1415, h1429, h1432, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1434 | h1434
                      · linarith only [h1333, h1413, h1434, h720, hc01, hc12, hlam, hphi]
                      · linarith only [h1415, h1429, h1434, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1437 | h1437
                  · linarith only [h1097, h1099, h1437, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1439 | h1439
                    · linarith only [h1097, h1099, h1439, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1441 | h1441
                      · linarith only [h1413, h1429, h1441, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1443 | h1443
                        · linarith only [h1413, h1429, h1437, h1443, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1415, h1443, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h0, h1098, h1414, hlam]
          · linarith only [h0, h1098, h1413, hc24, hlam, hphi, u2ehi4]
    · linarith only [h1097, h1098, hc25, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1449 | h1449
    · linarith only [h1097, h1449, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1451 | h1451
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1452 | h1452
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1453 | h1453
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1454 | h1454
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1455 | h1455
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1456 | h1456
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1457 | h1457
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1458 | h1458
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1459 | h1459
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1460 | h1460
                        · rcases h0bigk with h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, hlam, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1451, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1461_1, u3ehi4]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h720, hlam, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h970, hlam, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1449, h1453, h1459, hc01, hc12, hlam, hphi, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1097, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1449, h1452, hlam, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1449, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1097, hc01, hc23, hlam, hphi, ht12, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1461_1, u2ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1097, h1449, h1452, hc23, hlam, hphi, p1461_1, u2ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1097, h1449, hc23, hlam, hphi, p1461_1, u2ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h720, hc01, hc14, hlam, hphi, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1453, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1453, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1461_1, u3ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1449, h1453, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h970, hc01, hc15, hlam, hphi, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1449, h1453, h1459, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1451, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1452, hlam, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                        · linarith only [h1453, h1459, h1460, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1449, h1452, h1459, hlam]
                    · linarith only [h1097, h1458, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1451, h1457, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1452, h1456, h720, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1492 | h1492
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1493 | h1493
                  · linarith only [h1449, h1454, h1455, h1492, h1493, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h1097, h1493, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1452, h1492, h720, hlam]
            · linarith only [h1453, h1454, hc25, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1498 | h1498
            · linarith only [h1453, h1498, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1500 | h1500
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1501 | h1501
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1502 | h1502
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1503 | h1503
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1504 | h1504
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                        · rcases h0bigk with h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h0, hlam, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1451, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1506_1, u3ehi4]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h720, hlam, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h970, hlam, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h0, h1498, h1502, h1504, hc01, hc23, hlam, hphi, ht12, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1097, hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1449, h1452, hlam, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1449, hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1097, hc01, hc23, hlam, hphi, ht12, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1506_1, u2ehi0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1097, h1452, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1097, h1449, hc23, hlam, hphi, p1506_1, u2ehi0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h720, hc01, hc14, hlam, hphi, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1453, h1502, h720, hc23, hlam, hphi, p1506_1, u2ehi0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1453, h1502, h720, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1506_1, u3ehi0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1449, h1453, h1502, h720, hc23, hlam, hphi, p1506_1, u2ehi0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h970, hc01, hc15, hlam, hphi, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1449, h1502, h1504, hc23, hlam, hphi, p1506_1, u2ehi0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1451, hlam, p1506_0]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [h1452, hlam, p1506_1]
                          · have p1506_0 := h1506c.1
                            have p1506_1 := h1506c.2.1
                            have p1506_2 := h1506c.2.2.1
                            have p1506_3 := h1506c.2.2.2
                            linarith only [hlam, p1506_0]
                        · rcases h0bigk with h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h0, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1532_1, u3ehi0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h720, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h970, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h0, h1498, h1502, h1504, hc01, hc23, hlam, hphi, ht12, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1097, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h0, h1498, h1502, h1504, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1449, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1097, hc01, hc23, hlam, hphi, ht12, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1532_1, u2ehi0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1097, h720, hc01, hc23, hlam, hphi, ht12, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1097, h1449, hc23, hlam, hphi, p1532_1, u2ehi0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1453, h1502, h720, hc01, hc23, hlam, hphi, ht12, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1453, h1502, h720, hc23, hlam, hphi, p1532_1, u2ehi0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1453, h1502, h720, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1532_1, u3ehi0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1452, h1453, h1502, h1505, h720, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1532_1, u3ehi3]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1498, h1502, h1504, h970, hc01, hc23, hlam, hphi, ht12, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1498, h1502, h1504, h970, hc23, hlam, hphi, p1532_1, u2ehi0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1451, hlam, p1532_0]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [h1452, hlam, p1532_1]
                          · have p1532_0 := h1532c.1
                            have p1532_1 := h1532c.2.1
                            have p1532_2 := h1532c.2.2.1
                            have p1532_3 := h1532c.2.2.2
                            linarith only [hlam, p1532_0]
                      · linarith only [h1452, h1453, h1504, h720, hlam]
                    · linarith only [h1097, h1503, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1502, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1452, h1501, h720, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1562 | h1562
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1563 | h1563
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1564 | h1564
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1565 | h1565
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1566 | h1566
                        · rcases h0bigk with h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h0, hlam, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1451, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1567_1, u3ehi4]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h720, hlam, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h970, hlam, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h0, h1498, h1500, h1562, h1563, hc01, hc23, hlam, hphi, ht12, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1097, hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h0, h1498, h1500, h1562, h1563, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1449, hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1097, hc01, hc23, hlam, hphi, ht12, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1567_1, u2ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1097, h1449, h1452, hc23, hlam, hphi, p1567_1, u2ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1097, h1449, hc23, hlam, hphi, p1567_1, u2ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1500, h1563, h720, hc01, hc23, hlam, hphi, ht12, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1500, h1563, h720, hc23, hlam, hphi, p1567_1, u2ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1500, h1563, h720, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1567_1, u3ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1449, h1500, h1563, h720, hc23, hlam, hphi, p1567_1, u2ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1500, h1562, h1563, h970, hc01, hc23, hlam, hphi, ht12, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1500, h1562, h1563, h970, hc23, hlam, hphi, p1567_1, u2ehi0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1451, hlam, p1567_0]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [h1452, hlam, p1567_1]
                          · have p1567_0 := h1567c.1
                            have p1567_1 := h1567c.2.1
                            have p1567_2 := h1567c.2.2.1
                            have p1567_3 := h1567c.2.2.2
                            linarith only [hlam, p1567_0]
                        · linarith only [h1452, h1500, h1566, h720, hlam]
                      · linarith only [h1452, h1500, h1563, h1565, h720, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h1451, h1500, h1563, h1564, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h1097, h1563, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1452, h1562, h720, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1598 | h1598
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1599 | h1599
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1601 | h1601
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1602 | h1602
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1603 | h1603
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1604 | h1604
                      · linarith only [h1452, h1598, h1604, h720, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1606 | h1606
                        · linarith only [h1449, h1602, h1604, h1606, hc24, hlam, hphi, u2ehi0]
                        · rcases h0bigk with h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h0, hlam, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1608_1, u3ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h720, hlam, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h970, hlam, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1449, h1598, h1601, h1604, hc01, hc12, hlam, hphi, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1097, hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1449, h1598, h1601, h1604, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1449, hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1097, h1449, h1598, h1601, h1604, hc01, hc12, hc23, hlam, hphi, p1608_1, u2ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1608_1, u2ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1097, h1449, h1598, h1601, h1604, h720, hc01, hc12, hc23, hlam, hphi, p1608_1, u2ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1097, h1449, h1598, h1601, h1604, h970, hc01, hc12, hc23, hlam, hphi, p1608_1, u2ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1598, h720, hc01, hc12, hlam, hphi, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1608_1, u2ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1608_1, u3ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1452, hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1598, h1601, h970, hc01, hc12, hlam, hphi, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1449, h1598, h1601, h1604, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1608_1, u2ehi0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1451, hlam, p1608_0]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [h1449, h1598, h1601, h1604, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1608_1]
                          · have p1608_0 := h1608c.1
                            have p1608_1 := h1608c.2.1
                            have p1608_2 := h1608c.2.2.1
                            have p1608_3 := h1608c.2.2.2
                            linarith only [hlam, p1608_0]
                    · linarith only [h1097, h1603, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1451, h1602, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1636 | h1636
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1637 | h1637
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1638 | h1638
                      · linarith only [h1598, h1601, h1638, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1640 | h1640
                        · linarith only [h1598, h1601, h1636, h1640, hlam]
                        · rcases h0bigk with h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h0, hlam, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1451, h1640, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1642_1, u3ehi3]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h720, hlam, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h970, hlam, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1449, hc01, hc25, hlam, hphi, ht12, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1097, hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1449, h1599, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1449, hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1097, hc01, hc23, hlam, hphi, ht12, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1642_1, u2ehi0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1097, h720, hc01, hc23, hlam, hphi, ht12, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1097, h970, hc01, hc23, hlam, hphi, ht12, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1601, h720, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1642_1, u2ehi0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1601, h720, hc45, hlam, hphi, ht34, p1642_1, u3ehi0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1452, hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1449, h1599, hc01, hc12, hlam, hphi, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1449, h1599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1642_1, u2ehi0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1451, hlam, p1642_0]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [h1449, h1599, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1642_1]
                          · have p1642_0 := h1642c.1
                            have p1642_1 := h1642c.2.1
                            have p1642_2 := h1642c.2.2.1
                            have p1642_3 := h1642c.2.2.2
                            linarith only [hlam, p1642_0]
                    · linarith only [h1097, h1637, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1451, h1636, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1670 | h1670
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1671 | h1671
                  · linarith only [h1452, h1600, h1670, h1671, h720, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1097, h1671, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1674 | h1674
                  · linarith only [h1598, h1600, h1674, hlam]
                  · linarith only [h1097, h1674, hc34, hlam, hphi, ht23, u2ehi0]
            · linarith only [h1598, h1599, hc25, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1678 | h1678
            · linarith only [h1449, h1598, h1678, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1681 | h1681
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1682 | h1682
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1683 | h1683
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1684 | h1684
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1685 | h1685
                        · linarith only [h1449, h1452, h1682, h1685, hc23, hlam, hphi, u2ehi0]
                        · rcases h0bigk with h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h0, hlam, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1687_1, u3ehi0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h720, hlam, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h970, hlam, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1097, hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1449, h1452, h1598, h1681, h1682, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1449, hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1097, hc01, hc23, hlam, hphi, ht12, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1097, hc23, hlam, hphi, p1687_1, u2ehi0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1097, h720, hc01, hc23, hlam, hphi, ht12, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1097, h970, hc01, hc23, hlam, hphi, ht12, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1598, h1682, h720, hc01, hc23, hlam, hphi, ht12, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1452, h1598, h1681, h1682, hc23, hlam, hphi, p1687_1, u2ehi0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1452, h1598, h1681, h1682, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1687_1, u3ehi0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1452, hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1598, h1681, h1682, h970, hc01, hc23, hlam, hphi, ht12, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1598, h1681, h1682, h970, hc23, hlam, hphi, p1687_1, u2ehi0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1451, hlam, p1687_0]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [h1452, h1598, h1681, h1682, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1687_1]
                          · have p1687_0 := h1687c.1
                            have p1687_1 := h1687c.2.1
                            have p1687_2 := h1687c.2.2.1
                            have p1687_3 := h1687c.2.2.2
                            linarith only [hlam, p1687_0]
                      · linarith only [h1598, h1681, h1684, hlam]
                    · linarith only [h1097, h1451, h1683, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h1097, h1682, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1716 | h1716
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1717 | h1717
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1718 | h1718
                      · linarith only [h1681, h1716, h1718, h720, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1598, h1718, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1097, h1717, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1716, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1723 | h1723
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                  · linarith only [h1452, h1680, h1723, h1724, h720, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1097, h1724, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1727 | h1727
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1728 | h1728
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1729 | h1729
                      · linarith only [h0, h1598, h1723, h1727, h1729, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1598, h1729, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1097, h1728, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1451, h1727, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1734 | h1734
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1735 | h1735
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1736 | h1736
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1737 | h1737
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1738 | h1738
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1739 | h1739
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1740 | h1740
                    · linarith only [h1097, h1451, h1740, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1097, h1740, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1739, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1734, h1738, h720, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1746 | h1746
                  · linarith only [h1449, h1736, h1737, h1745, h1746, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h1097, h1746, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1734, h1745, h720, hlam]
            · linarith only [h1735, h1736, hc25, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1751 | h1751
            · linarith only [h1735, h1751, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1753 | h1753
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1754 | h1754
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1755 | h1755
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1756 | h1756
                    · linarith only [h1097, h1451, h1756, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1735, h1755, h1756, hc35, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h1097, h1755, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1734, h1754, h720, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1761 | h1761
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1762 | h1762
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1763 | h1763
                    · linarith only [h1097, h1451, h1763, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1753, h1762, h1763, hc35, hlam, hphi, u3ehi1]
                  · linarith only [h1097, h1762, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1734, h1761, h720, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1768 | h1768
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1769 | h1769
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1770 | h1770
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1772 | h1772
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1773 | h1773
                    · linarith only [h1097, h1451, h1773, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1772, h1773, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1097, h1772, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1777 | h1777
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1778 | h1778
                    · linarith only [h1097, h1451, h1778, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1097, h1778, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1777, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1782 | h1782
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1783 | h1783
                  · linarith only [h1097, h1451, h1734, h1770, h1782, h1783, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h1097, h1783, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1786 | h1786
                  · linarith only [h1768, h1770, h1782, h1786, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h1097, h1786, hc34, hlam, hphi, ht23, u2ehi0]
            · linarith only [h1768, h1769, hc25, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1790 | h1790
            · linarith only [h1768, h1790, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1792 | h1792
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1793 | h1793
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1794 | h1794
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1795 | h1795
                    · linarith only [h1097, h1451, h1795, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1768, h1794, h1795, hc35, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h1097, h1794, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1799 | h1799
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1800 | h1800
                    · linarith only [h1097, h1451, h1800, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1097, h1800, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1792, h1793, h1799, hc45, hlam, hphi, ht23, ht34, u2ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1804 | h1804
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1805 | h1805
                  · linarith only [h1097, h1451, h1734, h1792, h1804, h1805, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h1097, h1805, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1808 | h1808
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1809 | h1809
                    · linarith only [h1097, h1451, h1809, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1097, h1809, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1097, h1808, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 3626000 in
set_option maxHeartbeats 3626000 in
theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h720 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h970 | h970
  · exact r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h720 h970
  · exact r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h720 h970

set_option maxHeartbeats 3626000 in
set_option maxHeartbeats 3626000 in
theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h720 | h720
  · exact r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h720
  · exact r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h720

end R2N4
