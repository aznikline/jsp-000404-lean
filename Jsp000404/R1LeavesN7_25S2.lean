import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h859 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h969 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1027 | h1027
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1028 | h1028
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1029 | h1029
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1030 | h1030
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1031 | h1031
            · rcases h2bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                rcases p1032_3 (m.d 0 2) (by simp) with h1034 | h1034
                · rcases p1032_3 (m.d 1 2) (by simp) with h1035 | h1035
                  · linarith only [h0, h1035, hlam]
                  · rcases p1032_3 (m.d 2 3) (by simp) with h1037 | h1037
                    · linarith only [h1037, h2, hlam]
                    · linarith only [h1037, h7, hlam]
                · linarith only [h0, h1034, hlam]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h0, h1026, h1031, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1032_1]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                rcases p1032_3 (m.d 0 2) (by simp) with h1042 | h1042
                · rcases p1032_3 (m.d 1 2) (by simp) with h1043 | h1043
                  · linarith only [h0, h1043, hlam]
                  · rcases p1032_3 (m.d 2 3) (by simp) with h1045 | h1045
                    · linarith only [h1045, h2, hlam]
                    · linarith only [h1028, h1045, hlam]
                · linarith only [h1042, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                rcases p1032_3 (m.d 0 2) (by simp) with h1049 | h1049
                · rcases p1032_3 (m.d 1 2) (by simp) with h1050 | h1050
                  · linarith only [h0, h1050, hlam]
                  · rcases p1032_3 (m.d 2 3) (by simp) with h1052 | h1052
                    · linarith only [h1052, h2, hlam]
                    · linarith only [h1029, h1052, hlam]
                · linarith only [h1049, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h0, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h7, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h859, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h969, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h2, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                rcases p1032_3 (m.d 0 2) (by simp) with h1062 | h1062
                · rcases p1032_3 (m.d 1 2) (by simp) with h1063 | h1063
                  · linarith only [h1063, hlam, p1032_0]
                  · rcases p1032_3 (m.d 2 3) (by simp) with h1065 | h1065
                    · rcases p1032_3 (m.d 2 4) (by simp) with h1066 | h1066
                      · linarith only [h1028, h1066, hlam]
                      · linarith only [h1066, h859, hlam]
                    · linarith only [h1065, hlam, p1032_0]
                · linarith only [h0, h1062, hlam]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h1030, h969, hc12, hc23, hlam, hphi, p1032_1]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h0, h2, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h3, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                rcases p1032_3 (m.d 0 2) (by simp) with h1075 | h1075
                · rcases p1032_3 (m.d 1 2) (by simp) with h1076 | h1076
                  · linarith only [h1076, hlam, p1032_0]
                  · rcases p1032_3 (m.d 2 3) (by simp) with h1078 | h1078
                    · rcases p1032_3 (m.d 2 4) (by simp) with h1079 | h1079
                      · rcases p1032_3 (m.d 2 5) (by simp) with h1080 | h1080
                        · linarith only [h1030, h1080, hlam]
                        · linarith only [h1080, h969, hlam]
                      · linarith only [h1079, hlam, p1032_0]
                    · linarith only [h1078, h7, hlam]
                · linarith only [h0, h1075, hlam]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h1028, hlam, p1032_1]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h969, hc12, hc24, hlam, hphi, p1032_1]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h4, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                rcases p1032_3 (m.d 0 2) (by simp) with h1090 | h1090
                · rcases p1032_3 (m.d 1 2) (by simp) with h1091 | h1091
                  · linarith only [h1091, hlam, p1032_0]
                  · rcases p1032_3 (m.d 2 3) (by simp) with h1093 | h1093
                    · rcases p1032_3 (m.d 2 4) (by simp) with h1094 | h1094
                      · rcases p1032_3 (m.d 2 5) (by simp) with h1095 | h1095
                        · rcases h3bigk with h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h1026, h1031, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h1031, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            rcases p1096_3 (m.d 0 3) (by simp) with h1101 | h1101
                            · rcases p1096_3 (m.d 1 3) (by simp) with h1102 | h1102
                              · linarith only [h1, h1102, hlam]
                              · linarith only [h1027, h1102, hlam]
                            · linarith only [h1101, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h7, hlam, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1031, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h2, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h2, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h1031, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h0, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h5, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1026, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1028, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1026, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p1096_1]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h6, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1027, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1029, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [h1031, hlam, p1096_0]
                          · have p1096_0 := h1096c.1
                            have p1096_1 := h1096c.2.1
                            have p1096_2 := h1096c.2.2.1
                            have p1096_3 := h1096c.2.2.2
                            linarith only [hlam, p1096_0]
                        · linarith only [h1095, hlam, p1032_0]
                      · linarith only [h1094, h859, hlam]
                    · linarith only [h1093, h7, hlam]
                · linarith only [h0, h1090, hlam]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h1029, hlam, p1032_1]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [h1030, hlam, p1032_0]
              · have p1032_0 := h1032c.1
                have p1032_1 := h1032c.2.1
                have p1032_2 := h1032c.2.2.1
                have p1032_3 := h1032c.2.2.2
                linarith only [hlam, p1032_0]
            · rcases h2bigk with h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                rcases p1133_3 (m.d 0 2) (by simp) with h1135 | h1135
                · rcases p1133_3 (m.d 1 2) (by simp) with h1136 | h1136
                  · linarith only [h0, h1136, hlam]
                  · rcases p1133_3 (m.d 2 3) (by simp) with h1138 | h1138
                    · linarith only [h1138, h2, hlam]
                    · linarith only [h1138, h7, hlam]
                · linarith only [h0, h1135, hlam]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h0, h1028, h1030, h1031, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h0, h1030, h1031, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                rcases p1133_3 (m.d 0 2) (by simp) with h1144 | h1144
                · rcases p1133_3 (m.d 1 2) (by simp) with h1145 | h1145
                  · linarith only [h0, h1145, hlam]
                  · rcases p1133_3 (m.d 2 3) (by simp) with h1147 | h1147
                    · linarith only [h1147, h2, hlam]
                    · linarith only [h1029, h1147, hlam]
                · linarith only [h1144, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h0, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h7, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h859, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h969, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h2, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                rcases p1133_3 (m.d 0 2) (by simp) with h1157 | h1157
                · rcases p1133_3 (m.d 1 2) (by simp) with h1158 | h1158
                  · linarith only [h1158, hlam, p1133_0]
                  · rcases p1133_3 (m.d 2 3) (by simp) with h1160 | h1160
                    · rcases p1133_3 (m.d 2 4) (by simp) with h1161 | h1161
                      · linarith only [h1028, h1161, hlam]
                      · linarith only [h1161, h859, hlam]
                    · linarith only [h1160, hlam, p1133_0]
                · linarith only [h0, h1157, hlam]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h1030, h1031, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h0, h2, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h3, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                rcases p1133_3 (m.d 0 2) (by simp) with h1170 | h1170
                · rcases p1133_3 (m.d 1 2) (by simp) with h1171 | h1171
                  · linarith only [h1171, hlam, p1133_0]
                  · rcases p1133_3 (m.d 2 3) (by simp) with h1173 | h1173
                    · rcases p1133_3 (m.d 2 4) (by simp) with h1174 | h1174
                      · rcases p1133_3 (m.d 2 5) (by simp) with h1175 | h1175
                        · linarith only [h1030, h1175, hlam]
                        · linarith only [h1175, h969, hlam]
                      · linarith only [h1174, hlam, p1133_0]
                    · linarith only [h1173, h7, hlam]
                · linarith only [h0, h1170, hlam]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h1028, hlam, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h969, hc12, hc24, hlam, hphi, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h4, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                rcases p1133_3 (m.d 0 2) (by simp) with h1185 | h1185
                · rcases p1133_3 (m.d 1 2) (by simp) with h1186 | h1186
                  · linarith only [h1186, hlam, p1133_0]
                  · rcases p1133_3 (m.d 2 3) (by simp) with h1188 | h1188
                    · rcases p1133_3 (m.d 2 4) (by simp) with h1189 | h1189
                      · rcases p1133_3 (m.d 2 5) (by simp) with h1190 | h1190
                        · rcases h3bigk with h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h0, h1026, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h0, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            rcases p1191_3 (m.d 0 3) (by simp) with h1195 | h1195
                            · rcases p1191_3 (m.d 1 3) (by simp) with h1196 | h1196
                              · linarith only [h1, h1196, hlam]
                              · linarith only [h1026, h1196, hlam]
                            · linarith only [h1195, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            rcases p1191_3 (m.d 0 3) (by simp) with h1200 | h1200
                            · rcases p1191_3 (m.d 1 3) (by simp) with h1201 | h1201
                              · linarith only [h1, h1201, hlam]
                              · linarith only [h1027, h1201, hlam]
                            · linarith only [h1200, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h7, hlam, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h0, h1031, h2, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h2, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h0, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h0, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h0, h1031, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h5, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1026, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1028, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1031, hlam, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h6, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1027, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1029, hlam, p1191_0]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [h1027, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1191_1]
                          · have p1191_0 := h1191c.1
                            have p1191_1 := h1191c.2.1
                            have p1191_2 := h1191c.2.2.1
                            have p1191_3 := h1191c.2.2.2
                            linarith only [hlam, p1191_0]
                        · linarith only [h1190, hlam, p1133_0]
                      · linarith only [h1189, h859, hlam]
                    · linarith only [h1188, h7, hlam]
                · linarith only [h0, h1185, hlam]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h1029, hlam, p1133_1]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [h1030, hlam, p1133_0]
              · have p1133_0 := h1133c.1
                have p1133_1 := h1133c.2.1
                have p1133_2 := h1133c.2.2.1
                have p1133_3 := h1133c.2.2.2
                linarith only [hlam, p1133_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1232 | h1232
            · linarith only [h0, h1030, h1232, h2, h5, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                rcases p1234_3 (m.d 0 2) (by simp) with h1236 | h1236
                · rcases p1234_3 (m.d 1 2) (by simp) with h1237 | h1237
                  · linarith only [h0, h1237, hlam]
                  · rcases p1234_3 (m.d 2 3) (by simp) with h1239 | h1239
                    · linarith only [h1239, h2, hlam]
                    · linarith only [h1239, h7, hlam]
                · linarith only [h0, h1236, hlam]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                rcases p1234_3 (m.d 0 2) (by simp) with h1243 | h1243
                · rcases p1234_3 (m.d 1 2) (by simp) with h1244 | h1244
                  · linarith only [h0, h1244, hlam]
                  · rcases p1234_3 (m.d 2 3) (by simp) with h1246 | h1246
                    · linarith only [h1246, hlam, p1234_0]
                    · rcases p1234_3 (m.d 2 4) (by simp) with h1248 | h1248
                      · linarith only [h1248, h3, hlam]
                      · rcases p1234_3 (m.d 2 5) (by simp) with h1250 | h1250
                        · linarith only [h1250, h4, hlam]
                        · rcases h3bigk with h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h0, h1027, h1232, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h0, h1029, h1030, h2, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            rcases p1252_3 (m.d 0 3) (by simp) with h1256 | h1256
                            · rcases p1252_3 (m.d 1 3) (by simp) with h1257 | h1257
                              · linarith only [h1, h1257, hlam]
                              · linarith only [h1026, h1257, hlam]
                            · linarith only [h1256, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            rcases p1252_3 (m.d 0 3) (by simp) with h1261 | h1261
                            · rcases p1252_3 (m.d 1 3) (by simp) with h1262 | h1262
                              · linarith only [h1, h1262, hlam]
                              · linarith only [h1027, h1262, hlam]
                            · linarith only [h1261, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h7, hlam, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h0, h1232, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1234_1, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h2, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1234_1, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1234_1, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h0, h1232, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1234_1, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h5, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1026, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1028, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1232, hlam, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h6, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1027, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1029, hlam, p1252_0]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [h1027, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1252_1]
                          · have p1252_0 := h1252c.1
                            have p1252_1 := h1252c.2.1
                            have p1252_2 := h1252c.2.2.1
                            have p1252_3 := h1252c.2.2.2
                            linarith only [hlam, p1252_0]
                · linarith only [h1243, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                rcases p1234_3 (m.d 0 2) (by simp) with h1287 | h1287
                · rcases p1234_3 (m.d 1 2) (by simp) with h1288 | h1288
                  · linarith only [h0, h1288, hlam]
                  · rcases p1234_3 (m.d 2 3) (by simp) with h1290 | h1290
                    · linarith only [h1290, h2, hlam]
                    · linarith only [h1028, h1290, hlam]
                · linarith only [h1287, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                rcases p1234_3 (m.d 0 2) (by simp) with h1294 | h1294
                · rcases p1234_3 (m.d 1 2) (by simp) with h1295 | h1295
                  · linarith only [h0, h1295, hlam]
                  · rcases p1234_3 (m.d 2 3) (by simp) with h1297 | h1297
                    · linarith only [h1297, h2, hlam]
                    · linarith only [h1029, h1297, hlam]
                · linarith only [h1294, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h0, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h7, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h859, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h969, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h2, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                rcases p1234_3 (m.d 0 2) (by simp) with h1307 | h1307
                · rcases p1234_3 (m.d 1 2) (by simp) with h1308 | h1308
                  · linarith only [h1308, hlam, p1234_0]
                  · rcases p1234_3 (m.d 2 3) (by simp) with h1310 | h1310
                    · rcases p1234_3 (m.d 2 4) (by simp) with h1311 | h1311
                      · linarith only [h1028, h1311, hlam]
                      · linarith only [h1311, h859, hlam]
                    · linarith only [h1310, hlam, p1234_0]
                · linarith only [h0, h1307, hlam]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h0, h2, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h0, h2, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h3, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h1030, hc12, hc45, hlam, hphi, ht23, ht34, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h1028, hlam, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h1030, hlam, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h4, hlam, p1234_0]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                rcases p1234_3 (m.d 0 2) (by simp) with h1325 | h1325
                · rcases p1234_3 (m.d 1 2) (by simp) with h1326 | h1326
                  · linarith only [h1326, hlam, p1234_0]
                  · rcases p1234_3 (m.d 2 3) (by simp) with h1328 | h1328
                    · rcases p1234_3 (m.d 2 4) (by simp) with h1329 | h1329
                      · linarith only [h1030, h1329, hlam]
                      · linarith only [h1329, h859, hlam]
                    · linarith only [h1328, h7, hlam]
                · linarith only [h0, h1325, hlam]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h1029, hlam, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [h0, h4, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1234_1]
              · have p1234_0 := h1234c.1
                have p1234_1 := h1234c.2.1
                have p1234_2 := h1234c.2.2.1
                have p1234_3 := h1234c.2.2.2
                linarith only [hlam, p1234_0]
        · linarith only [h1027, h1029, h7, hlam]
      · linarith only [h1026, h1028, h7, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1340 | h1340
        · linarith only [h0, h1026, h1027, h1340, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1342 | h1342
          · linarith only [h1339, h1340, h1342, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1344 | h1344
            · linarith only [h1026, h1342, h1344, h859, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h1339, h1340, h2, h6, h859, hlam, p1346_2]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                rcases p1346_3 (m.d 0 2) (by simp) with h1349 | h1349
                · rcases p1346_3 (m.d 1 2) (by simp) with h1350 | h1350
                  · linarith only [h0, h1350, hlam]
                  · rcases p1346_3 (m.d 2 3) (by simp) with h1352 | h1352
                    · linarith only [h1352, hlam, p1346_0]
                    · rcases p1346_3 (m.d 2 4) (by simp) with h1354 | h1354
                      · linarith only [h1354, h3, hlam]
                      · rcases p1346_3 (m.d 2 5) (by simp) with h1356 | h1356
                        · linarith only [h1356, h4, hlam]
                        · linarith only [h1340, h1356, hlam]
                · linarith only [h1349, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                rcases p1346_3 (m.d 0 2) (by simp) with h1360 | h1360
                · rcases p1346_3 (m.d 1 2) (by simp) with h1361 | h1361
                  · linarith only [h0, h1361, hlam]
                  · rcases p1346_3 (m.d 2 3) (by simp) with h1363 | h1363
                    · linarith only [h1363, h2, hlam]
                    · linarith only [h1339, h1363, hlam]
                · linarith only [h1360, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                rcases p1346_3 (m.d 0 2) (by simp) with h1367 | h1367
                · rcases p1346_3 (m.d 1 2) (by simp) with h1368 | h1368
                  · linarith only [h0, h1368, hlam]
                  · rcases p1346_3 (m.d 2 3) (by simp) with h1370 | h1370
                    · linarith only [h1370, h2, hlam]
                    · rcases p1346_3 (m.d 2 4) (by simp) with h1372 | h1372
                      · linarith only [h1372, h3, hlam]
                      · rcases p1346_3 (m.d 2 5) (by simp) with h1374 | h1374
                        · linarith only [h1374, hlam, p1346_0]
                        · rcases h3bigk with h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1026, h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h0, h1339, h2, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            rcases p1376_3 (m.d 0 3) (by simp) with h1380 | h1380
                            · rcases p1376_3 (m.d 1 3) (by simp) with h1381 | h1381
                              · linarith only [h1, h1381, hlam]
                              · linarith only [h1026, h1381, hlam]
                            · linarith only [h1380, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h0, h1026, h1027, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h7, hlam, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1027, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h2, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h0, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h0, h1340, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1340, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h5, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1026, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1339, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1344, hlam, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h6, hlam, p1376_0]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h1026, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h0, h1339, h2, h6, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [h0, h2, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1376_1]
                          · have p1376_0 := h1376c.1
                            have p1376_1 := h1376c.2.1
                            have p1376_2 := h1376c.2.2.1
                            have p1376_3 := h1376c.2.2.2
                            linarith only [hlam, p1376_0]
                · linarith only [h1367, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h0, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h7, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h859, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h969, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h2, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h0, h1340, h2, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h859, hc12, hc23, hlam, hphi, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h1340, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h3, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h0, h1339, h1340, h2, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h1339, hlam, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h1342, hlam, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h4, hlam, p1346_0]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                rcases p1346_3 (m.d 0 2) (by simp) with h1423 | h1423
                · rcases p1346_3 (m.d 1 2) (by simp) with h1424 | h1424
                  · linarith only [h1424, hlam, p1346_0]
                  · rcases p1346_3 (m.d 2 3) (by simp) with h1426 | h1426
                    · linarith only [h1340, h1426, hlam]
                    · linarith only [h1426, h7, hlam]
                · linarith only [h0, h1423, hlam]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h0, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [h0, h1340, h2, h6, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1346_1]
              · have p1346_0 := h1346c.1
                have p1346_1 := h1346c.2.1
                have p1346_2 := h1346c.2.2.1
                have p1346_3 := h1346c.2.2.2
                linarith only [hlam, p1346_0]
      · linarith only [h1, h1026, h1339, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1434 | h1434
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1435 | h1435
      · linarith only [h0, h1026, h1434, h1435, h2, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1437 | h1437
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1438 | h1438
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1439 | h1439
            · rcases h2bigk with h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h1435, h1437, h2, h5, h969, hlam, p1440_2]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                rcases p1440_3 (m.d 0 2) (by simp) with h1443 | h1443
                · rcases p1440_3 (m.d 1 2) (by simp) with h1444 | h1444
                  · linarith only [h0, h1444, hlam]
                  · rcases p1440_3 (m.d 2 3) (by simp) with h1446 | h1446
                    · linarith only [h1446, hlam, p1440_0]
                    · rcases p1440_3 (m.d 2 4) (by simp) with h1448 | h1448
                      · linarith only [h1448, h3, hlam]
                      · linarith only [h1435, h1448, hlam]
                · linarith only [h1443, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                rcases p1440_3 (m.d 0 2) (by simp) with h1452 | h1452
                · rcases p1440_3 (m.d 1 2) (by simp) with h1453 | h1453
                  · linarith only [h0, h1453, hlam]
                  · rcases p1440_3 (m.d 2 3) (by simp) with h1455 | h1455
                    · linarith only [h1455, h2, hlam]
                    · rcases p1440_3 (m.d 2 4) (by simp) with h1457 | h1457
                      · linarith only [h1457, hlam, p1440_0]
                      · rcases p1440_3 (m.d 2 5) (by simp) with h1459 | h1459
                        · linarith only [h1459, h4, hlam]
                        · rcases h3bigk with h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h1434, h1439, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h1437, h2, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h1026, h1434, h1439, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            rcases p1461_3 (m.d 0 3) (by simp) with h1466 | h1466
                            · rcases p1461_3 (m.d 1 3) (by simp) with h1467 | h1467
                              · linarith only [h1, h1467, hlam]
                              · linarith only [h1434, h1467, hlam]
                            · linarith only [h1466, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h7, hlam, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1026, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1, h1439, hc01, hc45, hlam, hphi, ht0b, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h2, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1435, hc13, hc34, hlam, hphi, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1435, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h1435, h1439, hc01, hc45, hlam, hphi, ht0b, ht5b, p1440_1, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h5, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h1434, h1439, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h0, h1439, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1461_1]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h6, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1434, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1437, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [h1439, hlam, p1461_0]
                          · have p1461_0 := h1461c.1
                            have p1461_1 := h1461c.2.1
                            have p1461_2 := h1461c.2.2.1
                            have p1461_3 := h1461c.2.2.2
                            linarith only [hlam, p1461_0]
                · linarith only [h1452, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                rcases p1440_3 (m.d 0 2) (by simp) with h1492 | h1492
                · rcases p1440_3 (m.d 1 2) (by simp) with h1493 | h1493
                  · linarith only [h0, h1493, hlam]
                  · rcases p1440_3 (m.d 2 3) (by simp) with h1495 | h1495
                    · linarith only [h1495, h2, hlam]
                    · linarith only [h1437, h1495, hlam]
                · linarith only [h1492, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h0, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h7, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h859, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h969, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h2, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h0, h1435, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1440_1]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h1435, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h0, h1435, h2, h5, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1440_1]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h3, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                rcases p1440_3 (m.d 0 2) (by simp) with h1510 | h1510
                · rcases p1440_3 (m.d 1 2) (by simp) with h1511 | h1511
                  · linarith only [h1511, hlam, p1440_0]
                  · rcases p1440_3 (m.d 2 3) (by simp) with h1513 | h1513
                    · linarith only [h1435, h1513, hlam]
                    · linarith only [h1513, h7, hlam]
                · linarith only [h0, h1510, hlam]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h7, hc12, hc24, hlam, hphi, p1440_1]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h0, h1435, h2, h5, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1440_1]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h4, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h0, h1435, h1437, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1440_1]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h1437, hlam, p1440_1]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [h1438, hlam, p1440_0]
              · have p1440_0 := h1440c.1
                have p1440_1 := h1440c.2.1
                have p1440_2 := h1440c.2.2.1
                have p1440_3 := h1440c.2.2.2
                linarith only [hlam, p1440_0]
            · linarith only [h1435, h1439, h7, hc12, hc45, hlam, hphi, ht23, ht34]
          · linarith only [h1435, h1437, h1438, hlam]
        · linarith only [h1, h1434, h1437, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1528 | h1528
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1529 | h1529
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1530 | h1530
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1531 | h1531
            · rcases h2bigk with h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1026, h1528, h2, h7, hlam, p1532_2]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1528, h1531, hc02, hc45, hlam, hphi, ht0b, ht5b, p1532_1]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                rcases p1532_3 (m.d 0 2) (by simp) with h1536 | h1536
                · rcases p1532_3 (m.d 1 2) (by simp) with h1537 | h1537
                  · linarith only [h0, h1537, hlam]
                  · rcases p1532_3 (m.d 2 3) (by simp) with h1539 | h1539
                    · linarith only [h1539, h2, hlam]
                    · linarith only [h1528, h1539, hlam]
                · linarith only [h1536, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                rcases p1532_3 (m.d 0 2) (by simp) with h1543 | h1543
                · rcases p1532_3 (m.d 1 2) (by simp) with h1544 | h1544
                  · linarith only [h0, h1544, hlam]
                  · rcases p1532_3 (m.d 2 3) (by simp) with h1546 | h1546
                    · linarith only [h1546, h2, hlam]
                    · linarith only [h1529, h1546, hlam]
                · linarith only [h1543, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h0, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h7, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h859, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h969, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h2, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                rcases p1532_3 (m.d 0 2) (by simp) with h1556 | h1556
                · rcases p1532_3 (m.d 1 2) (by simp) with h1557 | h1557
                  · linarith only [h1557, hlam, p1532_0]
                  · rcases p1532_3 (m.d 2 3) (by simp) with h1559 | h1559
                    · rcases p1532_3 (m.d 2 4) (by simp) with h1560 | h1560
                      · linarith only [h1528, h1560, hlam]
                      · linarith only [h1560, h859, hlam]
                    · linarith only [h1559, hlam, p1532_0]
                · linarith only [h0, h1556, hlam]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1434, h1529, h1530, h7, hc12, hc23, hlam, hphi, p1532_1]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h0, h1434, h1529, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1532_1]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h3, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                rcases p1532_3 (m.d 0 2) (by simp) with h1569 | h1569
                · rcases p1532_3 (m.d 1 2) (by simp) with h1570 | h1570
                  · linarith only [h1570, hlam, p1532_0]
                  · rcases p1532_3 (m.d 2 3) (by simp) with h1572 | h1572
                    · rcases p1532_3 (m.d 2 4) (by simp) with h1573 | h1573
                      · rcases p1532_3 (m.d 2 5) (by simp) with h1574 | h1574
                        · linarith only [h1530, h1574, hlam]
                        · linarith only [h1574, h969, hlam]
                      · linarith only [h1573, hlam, p1532_0]
                    · linarith only [h1572, h7, hlam]
                · linarith only [h0, h1569, hlam]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1528, hlam, p1532_1]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1434, h1529, h7, hc12, hc24, hlam, hphi, p1532_1]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h4, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                rcases p1532_3 (m.d 0 2) (by simp) with h1584 | h1584
                · rcases p1532_3 (m.d 1 2) (by simp) with h1585 | h1585
                  · linarith only [h1585, hlam, p1532_0]
                  · rcases p1532_3 (m.d 2 3) (by simp) with h1587 | h1587
                    · rcases p1532_3 (m.d 2 4) (by simp) with h1588 | h1588
                      · rcases p1532_3 (m.d 2 5) (by simp) with h1589 | h1589
                        · rcases h3bigk with h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            rcases p1590_3 (m.d 0 3) (by simp) with h1592 | h1592
                            · rcases p1590_3 (m.d 1 3) (by simp) with h1593 | h1593
                              · linarith only [h1, h1593, hlam]
                              · rcases p1590_3 (m.d 2 3) (by simp) with h1595 | h1595
                                · linarith only [h1595, h2, hlam]
                                · linarith only [h1595, h7, hlam]
                            · linarith only [h1, h1592, hlam]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h0, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h0, h1434, h1531, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h0, h1434, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h1, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h7, hlam, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h1026, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h1434, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h2, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h7, hc12, hc23, hlam, hphi, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h0, h1434, h1531, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h0, h1434, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h5, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h7, hc12, hc34, hlam, hphi, ht23, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h1528, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h0, h1434, h1528, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h6, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h7, hc12, hc35, hlam, hphi, ht23, p1590_1]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h1529, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [h1531, hlam, p1590_0]
                          · have p1590_0 := h1590c.1
                            have p1590_1 := h1590c.2.1
                            have p1590_2 := h1590c.2.2.1
                            have p1590_3 := h1590c.2.2.2
                            linarith only [hlam, p1590_0]
                        · linarith only [h1589, hlam, p1532_0]
                      · linarith only [h1588, h859, hlam]
                    · linarith only [h1587, h7, hlam]
                · linarith only [h0, h1584, hlam]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1529, hlam, p1532_1]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [h1530, hlam, p1532_0]
              · have p1532_0 := h1532c.1
                have p1532_1 := h1532c.2.1
                have p1532_2 := h1532c.2.2.1
                have p1532_3 := h1532c.2.2.2
                linarith only [hlam, p1532_0]
            · linarith only [h0, h1026, h1528, h1530, h1531, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1630 | h1630
            · linarith only [h0, h1530, h1630, h2, h5, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h1434, h1529, h2, h7, hlam, p1632_2]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h0, h1434, h1529, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                rcases p1632_3 (m.d 0 2) (by simp) with h1636 | h1636
                · rcases p1632_3 (m.d 1 2) (by simp) with h1637 | h1637
                  · linarith only [h0, h1637, hlam]
                  · rcases p1632_3 (m.d 2 3) (by simp) with h1639 | h1639
                    · linarith only [h1639, h2, hlam]
                    · linarith only [h1528, h1639, hlam]
                · linarith only [h1636, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                rcases p1632_3 (m.d 0 2) (by simp) with h1643 | h1643
                · rcases p1632_3 (m.d 1 2) (by simp) with h1644 | h1644
                  · linarith only [h0, h1644, hlam]
                  · rcases p1632_3 (m.d 2 3) (by simp) with h1646 | h1646
                    · linarith only [h1646, h2, hlam]
                    · linarith only [h1529, h1646, hlam]
                · linarith only [h1643, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h0, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h7, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h859, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h969, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h2, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                rcases p1632_3 (m.d 0 2) (by simp) with h1656 | h1656
                · rcases p1632_3 (m.d 1 2) (by simp) with h1657 | h1657
                  · linarith only [h1657, hlam, p1632_0]
                  · rcases p1632_3 (m.d 2 3) (by simp) with h1659 | h1659
                    · rcases p1632_3 (m.d 2 4) (by simp) with h1660 | h1660
                      · linarith only [h1528, h1660, hlam]
                      · linarith only [h1660, h859, hlam]
                    · linarith only [h1659, hlam, p1632_0]
                · linarith only [h0, h1656, hlam]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h0, h1026, h1528, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h0, h2, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h3, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h1530, hc12, hc45, hlam, hphi, ht23, ht34, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h1528, hlam, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h1530, hlam, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h4, hlam, p1632_0]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                rcases p1632_3 (m.d 0 2) (by simp) with h1674 | h1674
                · rcases p1632_3 (m.d 1 2) (by simp) with h1675 | h1675
                  · linarith only [h1675, hlam, p1632_0]
                  · rcases p1632_3 (m.d 2 3) (by simp) with h1677 | h1677
                    · rcases p1632_3 (m.d 2 4) (by simp) with h1678 | h1678
                      · linarith only [h1530, h1678, hlam]
                      · linarith only [h1678, h859, hlam]
                    · linarith only [h1677, h7, hlam]
                · linarith only [h0, h1674, hlam]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h1529, hlam, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [h859, hc12, hc25, hlam, hphi, p1632_1]
              · have p1632_0 := h1632c.1
                have p1632_1 := h1632c.2.1
                have p1632_2 := h1632c.2.2.1
                have p1632_3 := h1632c.2.2.2
                linarith only [hlam, p1632_0]
        · linarith only [h1026, h1528, h1529, h7, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1687 | h1687
        · linarith only [h1434, h1528, h1687, h7, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1689 | h1689
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1690 | h1690
            · rcases h2bigk with h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h1528, h2, h5, h7, hlam, p1691_2]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                rcases p1691_3 (m.d 0 2) (by simp) with h1694 | h1694
                · rcases p1691_3 (m.d 1 2) (by simp) with h1695 | h1695
                  · linarith only [h0, h1695, hlam]
                  · rcases p1691_3 (m.d 2 3) (by simp) with h1697 | h1697
                    · linarith only [h1697, hlam, p1691_0]
                    · rcases p1691_3 (m.d 2 4) (by simp) with h1699 | h1699
                      · linarith only [h1699, h3, hlam]
                      · linarith only [h1528, h1699, hlam]
                · linarith only [h1694, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                rcases p1691_3 (m.d 0 2) (by simp) with h1703 | h1703
                · rcases p1691_3 (m.d 1 2) (by simp) with h1704 | h1704
                  · linarith only [h0, h1704, hlam]
                  · rcases p1691_3 (m.d 2 3) (by simp) with h1706 | h1706
                    · linarith only [h1706, h2, hlam]
                    · rcases p1691_3 (m.d 2 4) (by simp) with h1708 | h1708
                      · linarith only [h1708, hlam, p1691_0]
                      · rcases p1691_3 (m.d 2 5) (by simp) with h1710 | h1710
                        · linarith only [h1710, h4, hlam]
                        · rcases h3bigk with h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            rcases p1712_3 (m.d 0 3) (by simp) with h1714 | h1714
                            · rcases p1712_3 (m.d 1 3) (by simp) with h1715 | h1715
                              · linarith only [h1, h1715, hlam]
                              · rcases p1712_3 (m.d 2 3) (by simp) with h1717 | h1717
                                · linarith only [h1717, h2, hlam]
                                · linarith only [h1717, h7, hlam]
                            · linarith only [h1, h1714, hlam]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h1687, h1690, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h1687, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h1, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h7, hlam, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h1026, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h1434, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h2, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h7, hc12, hc23, hlam, hphi, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h1528, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h1687, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h5, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h2, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h6, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h7, hc12, hc35, hlam, hphi, ht23, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h0, h2, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1712_1]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [h1690, hlam, p1712_0]
                          · have p1712_0 := h1712c.1
                            have p1712_1 := h1712c.2.1
                            have p1712_2 := h1712c.2.2.1
                            have p1712_3 := h1712c.2.2.2
                            linarith only [hlam, p1712_0]
                · linarith only [h1703, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                rcases p1691_3 (m.d 0 2) (by simp) with h1745 | h1745
                · rcases p1691_3 (m.d 1 2) (by simp) with h1746 | h1746
                  · linarith only [h0, h1746, hlam]
                  · rcases p1691_3 (m.d 2 3) (by simp) with h1748 | h1748
                    · linarith only [h1748, h2, hlam]
                    · rcases p1691_3 (m.d 2 4) (by simp) with h1750 | h1750
                      · linarith only [h1750, h3, hlam]
                      · linarith only [h1689, h1750, hlam]
                · linarith only [h1745, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h0, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h7, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h859, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h969, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h2, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h0, h1528, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1691_1]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h1528, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h1687, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h3, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                rcases p1691_3 (m.d 0 2) (by simp) with h1765 | h1765
                · rcases p1691_3 (m.d 1 2) (by simp) with h1766 | h1766
                  · linarith only [h1766, hlam, p1691_0]
                  · rcases p1691_3 (m.d 2 3) (by simp) with h1768 | h1768
                    · linarith only [h1528, h1768, hlam]
                    · linarith only [h1768, h7, hlam]
                · linarith only [h0, h1765, hlam]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h7, hc12, hc24, hlam, hphi, p1691_1]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h0, h3, h969, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1691_1]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h4, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                rcases p1691_3 (m.d 0 2) (by simp) with h1776 | h1776
                · rcases p1691_3 (m.d 1 2) (by simp) with h1777 | h1777
                  · linarith only [h1777, hlam, p1691_0]
                  · rcases p1691_3 (m.d 2 3) (by simp) with h1779 | h1779
                    · linarith only [h1687, h1779, hlam]
                    · linarith only [h1779, h7, hlam]
                · linarith only [h0, h1776, hlam]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h7, hc12, hc25, hlam, hphi, p1691_1]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [h1689, hlam, p1691_0]
              · have p1691_0 := h1691c.1
                have p1691_1 := h1691c.2.1
                have p1691_2 := h1691c.2.2.1
                have p1691_3 := h1691c.2.2.2
                linarith only [hlam, p1691_0]
            · linarith only [h1528, h1689, h1690, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1787 | h1787
            · linarith only [h0, h1689, h1787, h2, h5, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1528, h1787, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h859 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 5 (by decide) (by decide) with h969 | h969
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h859 h969
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h859 h969

end R2N4
