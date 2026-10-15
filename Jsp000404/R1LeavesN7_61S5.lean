import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S3
import Jsp000404.R1LeavesN7_61S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3258000 in
set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h752 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1065 | h1065
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1066 | h1066
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1067 | h1067
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1068 | h1068
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1069 | h1069
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1070 | h1070
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1072 | h1072
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1074 | h1074
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1076 | h1076
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1077 | h1077
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1079 | h1079
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1080 | h1080
                                · rcases h5bigk with h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h1073, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1081_1, u2ehi4]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1081_1, u2ehi4]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1081_1, u2ehi4]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1068, hlam, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1073, hlam, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1068, hc02, hc35, hlam, hphi, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1065, h1071, h1073, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1069, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1075, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1078, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h0, h1066, h1069, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1070, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1076, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1079, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1080, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                · rcases h5bigk with h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1107_1, u2ehi4]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h1080, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1107_1, u2ehi4]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h1080, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1068, hlam, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1073, hlam, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h0, h1068, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1065, h1071, h1073, h1080, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1069, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1075, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1078, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1080, hlam, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1070, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1076, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1079, hlam, p1107_0]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [h1070, hc04, hc35, hlam, hphi, ht0b, ht5b, p1107_1]
                                  · have p1107_0 := h1107c.1
                                    have p1107_1 := h1107c.2.1
                                    have p1107_2 := h1107c.2.2.1
                                    have p1107_3 := h1107c.2.2.2
                                    linarith only [hlam, p1107_0]
                              · linarith only [h1065, h1071, h1076, h1079, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1065, h1071, h1075, h1078, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1135 | h1135
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1136 | h1136
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1137 | h1137
                                · rcases h5bigk with h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c | h1138c
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi4]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1138_1, u2ehi4]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h1137, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1068, hlam, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1073, hlam, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1074, h1077, h1135, h1137, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1065, h1071, h1073, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1069, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1075, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1135, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h0, h1066, h1069, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1138_1]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1070, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1076, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1136, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [h1137, hlam, p1138_0]
                                  · have p1138_0 := h1138c.1
                                    have p1138_1 := h1138c.2.1
                                    have p1138_2 := h1138c.2.2.1
                                    have p1138_3 := h1138c.2.2.2
                                    linarith only [hlam, p1138_0]
                                · linarith only [h1077, h1137, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1065, h1071, h1076, h1077, h1135, h1136, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                            · linarith only [h1065, h1071, h1075, h1135, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1167 | h1167
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1168 | h1168
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1169 | h1169
                              · linarith only [h1072, h1076, h1169, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1171 | h1171
                                · linarith only [h1072, h1076, h1167, h1171, hc23, hlam, hphi, u2ehi3]
                                · rcases h5bigk with h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1071, h1169, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1173_1, u2ehi3]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1071, h1076, h752, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1169, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1173_1, u2ehi3]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1076, hlam, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1068, hlam, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1073, hlam, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h0, h1068, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1169, hlam, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1069, hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1075, hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1168, hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1171, hlam, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1070, hlam, p1173_0]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1073, hc45, hlam, hphi, ht23, ht34, p1173_1, u2ehi4]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1070, h1071, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1173_1, u2ehi4]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [h1065, h1070, h1071, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1173_1]
                                  · have p1173_0 := h1173c.1
                                    have p1173_1 := h1173c.2.1
                                    have p1173_2 := h1173c.2.2.1
                                    have p1173_3 := h1173c.2.2.2
                                    linarith only [hlam, p1173_0]
                            · linarith only [h1065, h1071, h1075, h1168, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1065, h1070, h1071, h1074, h1076, h1167, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1075, h752, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1074, h752, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1065, h1068, h1071, h1073, h752, hc02, hlam, hphi, u0ehi4]
                · linarith only [h0, h1065, h1072, hc24, hlam, hphi, ht01, ht12, u0ehi4]
              · linarith only [h0, h1065, h1066, h1071, hc02, hlam, hphi, u0ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1206 | h1206
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1207 | h1207
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1209 | h1209
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1210 | h1210
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1211 | h1211
                        · linarith only [h1070, h1211, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1213 | h1213
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1214 | h1214
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1215 | h1215
                              · linarith only [h1065, h1070, h1207, h1211, h1215, hc01, hlam, hphi, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                                · linarith only [h1070, h1213, h1217, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                                · rcases h5bigk with h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1065, h1206, h1207, h1211, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1219_1, u2ehi3]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1065, h1206, h752, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1065, h1206, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1070, hlam, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1065, hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1219_1, u2ehi4]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1065, h1206, h752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1211, hlam, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1068, hlam, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1208, hlam, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h0, h1068, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1215, hlam, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1069, hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1210, hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1214, hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hlam, p1219_0]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1217, hlam, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1219_1, u0ehi4]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1208, hc45, hlam, hphi, ht23, ht34, p1219_1, u2ehi4]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht23, ht34, p1219_1, u2ehi4]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [h1217, hc34, hc45, hlam, hphi, p1219_1]
                                  · have p1219_0 := h1219c.1
                                    have p1219_1 := h1219c.2.1
                                    have p1219_2 := h1219c.2.2.1
                                    have p1219_3 := h1219c.2.2.2
                                    linarith only [hlam, p1219_0]
                            · linarith only [h1065, h1206, h1210, h1214, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1209, h1211, h1213, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1210, h752, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1065, h1208, h1209, h752, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h1206, h1208, h752, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h1065, h1070, h1206, h1207, h752, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · linarith only [h0, h1065, h1066, h1070, h1206, hc02, hlam, hphi, u0ehi3]
          · linarith only [h1065, h1069, h752, hlam]
        · linarith only [h1066, h1068, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1066, h1067, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1255 | h1255
      · linarith only [h1066, h1255, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1257 | h1257
        · linarith only [h1066, h1257, hc23, hlam, hphi, u2ehi4]
        · linarith only [h0, h1065, h1257, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1260 | h1260
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1261 | h1261
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1262 | h1262
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1264 | h1264
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1265 | h1265
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1266 | h1266
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1267 | h1267
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1269 | h1269
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1271 | h1271
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1272 | h1272
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1273 | h1273
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                                · rcases h5bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1065, hlam, p1275_1]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1263, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi4]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    rcases p1275_3 (m.d 0 5) (by simp) with h1279 | h1279
                                    · rcases p1275_3 (m.d 1 5) (by simp) with h1280 | h1280
                                      · rcases p1275_3 (m.d 2 5) (by simp) with h1281 | h1281
                                        · linarith only [h1262, h1281, hlam]
                                        · linarith only [h1272, h1281, hlam]
                                      · linarith only [h1269, h1280, hlam]
                                    · linarith only [h1263, h1279, hlam]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    rcases p1275_3 (m.d 0 5) (by simp) with h1286 | h1286
                                    · rcases p1275_3 (m.d 1 5) (by simp) with h1287 | h1287
                                      · rcases p1275_3 (m.d 2 5) (by simp) with h1288 | h1288
                                        · linarith only [h1262, h1288, hlam]
                                        · linarith only [h1273, h1288, hlam]
                                      · linarith only [h1270, h1287, hlam]
                                    · linarith only [h1264, h1286, hlam]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, p1275_1, u0ehi4]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi4]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    rcases p1275_3 (m.d 0 5) (by simp) with h1296 | h1296
                                    · linarith only [h1065, h1296, hlam]
                                    · linarith only [h1263, h1296, hlam]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    rcases p1275_3 (m.d 0 5) (by simp) with h1299 | h1299
                                    · linarith only [h1065, h1299, hlam]
                                    · linarith only [h1264, h1299, hlam]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1262, hlam, p1275_1]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1267, hlam, p1275_1]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1262, h1274, hc02, hc45, hlam, hphi, ht0b, ht5b, p1275_1]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h0, h1260, h1271, h1273, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1275_1]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1263, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1269, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1272, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1263, hc03, hc45, hlam, hphi, ht0b, ht5b, p1275_1]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1264, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1270, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1273, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [h1274, hlam, p1275_0]
                                  · have p1275_0 := h1275c.1
                                    have p1275_1 := h1275c.2.1
                                    have p1275_2 := h1275c.2.2.1
                                    have p1275_3 := h1275c.2.2.2
                                    linarith only [hlam, p1275_0]
                                · rcases h5bigk with h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1065, hlam, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1317_1, u2ehi4]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    rcases p1317_3 (m.d 0 5) (by simp) with h1321 | h1321
                                    · rcases p1317_3 (m.d 1 5) (by simp) with h1322 | h1322
                                      · rcases p1317_3 (m.d 2 5) (by simp) with h1323 | h1323
                                        · linarith only [h1262, h1323, hlam]
                                        · linarith only [h1272, h1323, hlam]
                                      · linarith only [h1269, h1322, hlam]
                                    · linarith only [h1263, h1321, hlam]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1065, h1265, h1268, h1270, h1274, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, p1317_1, u0ehi4]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1317_1, u2ehi4]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    rcases p1317_3 (m.d 0 5) (by simp) with h1332 | h1332
                                    · linarith only [h1065, h1332, hlam]
                                    · linarith only [h1263, h1332, hlam]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1274, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1262, hlam, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1267, hlam, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h0, h1262, h1274, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1262, h1274, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1263, hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1269, hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1272, hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1274, hlam, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1264, hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1270, hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1273, hlam, p1317_0]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [h1274, hc34, hc45, hlam, hphi, p1317_1]
                                  · have p1317_0 := h1317c.1
                                    have p1317_1 := h1317c.2.1
                                    have p1317_2 := h1317c.2.2.1
                                    have p1317_3 := h1317c.2.2.2
                                    linarith only [hlam, p1317_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1351 | h1351
                                · linarith only [h1273, h1351, hc34, hlam, hphi, ht23, u2ehi3]
                                · rcases h5bigk with h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1065, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1065, h1265, h1268, h1270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1353_1, u2ehi4]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    rcases p1353_3 (m.d 0 5) (by simp) with h1357 | h1357
                                    · rcases p1353_3 (m.d 1 5) (by simp) with h1358 | h1358
                                      · rcases p1353_3 (m.d 2 5) (by simp) with h1359 | h1359
                                        · linarith only [h1262, h1359, hlam]
                                        · linarith only [h1272, h1359, hlam]
                                      · linarith only [h1269, h1358, hlam]
                                    · linarith only [h1263, h1357, hlam]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1065, h1265, h1268, h1270, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1353_1, u2ehi3]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, p1353_1, u0ehi4]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1353_1, u2ehi3]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    rcases p1353_3 (m.d 0 5) (by simp) with h1368 | h1368
                                    · linarith only [h1065, h1368, hlam]
                                    · linarith only [h1263, h1368, hlam]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1353_1, u2ehi3]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1262, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1267, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h0, h1262, h1351, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1273, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1263, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1269, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1272, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1351, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1264, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1270, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht23, ht34, p1353_1, u2ehi4]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1351, hc34, hc45, hlam, hphi, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1387 | h1387
                              · linarith only [h1271, h1272, h1387, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1389 | h1389
                                · linarith only [h1387, h1389, hc34, hlam, hphi, ht23, u2ehi3]
                                · rcases h5bigk with h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1065, hlam, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1271, h1272, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1065, h1265, h1268, h1270, h1271, h1272, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1260, h1263, h1271, h1272, h1389, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, p1391_1, u0ehi4]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1271, h1272, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1271, h1272, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1271, h1272, h1389, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1262, hlam, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1267, hlam, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1272, hlam, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1387, hlam, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1263, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1269, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1264, h1271, h1272, h1389, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1389, hlam, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1264, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h1270, hlam, p1391_0]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h0, h1261, h1264, h1271, h1272, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi3]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [h0, h1261, h1264, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1391_1]
                                  · have p1391_0 := h1391c.1
                                    have p1391_1 := h1391c.2.1
                                    have p1391_2 := h1391c.2.2.1
                                    have p1391_3 := h1391c.2.2.2
                                    linarith only [hlam, p1391_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1417 | h1417
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1418 | h1418
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1419 | h1419
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
                                    linarith only [h1065, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1420_1, u2ehi4]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1424 | h1424
                                    · rcases p1420_3 (m.d 1 5) (by simp) with h1425 | h1425
                                      · rcases p1420_3 (m.d 2 5) (by simp) with h1426 | h1426
                                        · linarith only [h1262, h1426, hlam]
                                        · linarith only [h1417, h1426, hlam]
                                      · linarith only [h1269, h1425, hlam]
                                    · linarith only [h1263, h1424, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1431 | h1431
                                    · rcases p1420_3 (m.d 1 5) (by simp) with h1432 | h1432
                                      · rcases p1420_3 (m.d 2 5) (by simp) with h1433 | h1433
                                        · linarith only [h1262, h1433, hlam]
                                        · linarith only [h1418, h1433, hlam]
                                      · linarith only [h1270, h1432, hlam]
                                    · linarith only [h1264, h1431, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, p1420_1, u0ehi4]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1420_1, u2ehi4]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1441 | h1441
                                    · linarith only [h1065, h1441, hlam]
                                    · linarith only [h1263, h1441, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    rcases p1420_3 (m.d 0 5) (by simp) with h1444 | h1444
                                    · linarith only [h1065, h1444, hlam]
                                    · linarith only [h1264, h1444, hlam]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1262, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1267, hlam, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h0, h1262, h1419, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1265, h1268, h1271, h1417, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1263, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1269, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1417, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h0, h1260, h1263, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1420_1]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1264, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1270, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1418, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [h1419, hlam, p1420_0]
                                  · have p1420_0 := h1420c.1
                                    have p1420_1 := h1420c.2.1
                                    have p1420_2 := h1420c.2.2.1
                                    have p1420_3 := h1420c.2.2.2
                                    linarith only [hlam, p1420_0]
                                · linarith only [h1271, h1419, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1271, h1417, h1418, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1464 | h1464
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1465 | h1465
                                · rcases h5bigk with h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1065, hlam, p1466_1]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1417, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1466_1, u2ehi2]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1417, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1466_1, u2ehi2]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    rcases p1466_3 (m.d 0 5) (by simp) with h1471 | h1471
                                    · rcases p1466_3 (m.d 1 5) (by simp) with h1472 | h1472
                                      · rcases p1466_3 (m.d 2 5) (by simp) with h1473 | h1473
                                        · linarith only [h1262, h1473, hlam]
                                        · linarith only [h1464, h1473, hlam]
                                      · linarith only [h1270, h1472, hlam]
                                    · linarith only [h1264, h1471, hlam]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1265, h1268, h1270, hc12, hlam, hphi, ht01, p1466_1, u0ehi4]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1466_1, u2ehi2]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1265, h1268, h1270, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1466_1, u2ehi2]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    rcases p1466_3 (m.d 0 5) (by simp) with h1482 | h1482
                                    · linarith only [h1065, h1482, hlam]
                                    · linarith only [h1264, h1482, hlam]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1262, hlam, p1466_1]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1267, hlam, p1466_1]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1417, hlam, p1466_1]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h0, h1261, h1464, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1466_1]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1263, hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1269, hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht23, p1466_1, u2ehi4]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h0, h1260, h1263, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1466_1]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1264, hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1270, hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1464, hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [h1465, hlam, p1466_0]
                                  · have p1466_0 := h1466c.1
                                    have p1466_1 := h1466c.2.1
                                    have p1466_2 := h1466c.2.2.1
                                    have p1466_3 := h1466c.2.2.2
                                    linarith only [hlam, p1466_0]
                                · linarith only [h0, h1261, h1264, h1271, h1465, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1501 | h1501
                                · linarith only [h1464, h1501, hc34, hlam, hphi, ht23, u2ehi3]
                                · linarith only [h0, h1261, h1264, h1271, h1501, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h1065, h1261, h1264, h1270, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h0, h1260, h1263, h1269, h752, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h1268, h752, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1265, h1267, h752, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1260, h1266, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h1260, h1265, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1510 | h1510
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1511 | h1511
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1512 | h1512
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1513 | h1513
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1514 | h1514
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1515 | h1515
                        · linarith only [h1264, h1515, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1518 | h1518
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                              · linarith only [h1261, h1264, h1519, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1521 | h1521
                                · linarith only [h1065, h1260, h1515, h1517, h1521, hc02, hlam, hphi, u0ehi0]
                                · rcases h5bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1065, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1523_1, u2ehi4]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1065, h1515, h1521, hc34, hc45, hlam, hphi, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1264, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1515, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1523_1, u0ehi4]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1515, hc45, hlam, hphi, ht23, ht34, p1523_1, u2ehi4]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1515, h1521, hc34, hc45, hlam, hphi, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1515, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1262, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1512, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h0, h1262, h1521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1519, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1263, hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1514, hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1518, hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hlam, p1523_0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1521, hlam, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1264, hc04, hc45, hlam, hphi, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1065, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1523_1, u0ehi0]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht23, ht34, p1523_1, u2ehi4]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [h1521, hc34, hc45, hlam, hphi, p1523_1]
                                  · have p1523_0 := h1523c.1
                                    have p1523_1 := h1523c.2.1
                                    have p1523_2 := h1523c.2.2.1
                                    have p1523_3 := h1523c.2.2.2
                                    linarith only [hlam, p1523_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1549 | h1549
                              · linarith only [h0, h1260, h1263, h1515, h1517, h1518, h1549, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1551 | h1551
                                · linarith only [h0, h1065, h1260, h1263, h1515, h1517, h1518, h1551, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi0, u2ehi3]
                                · rcases h5bigk with h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1065, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1517, h1518, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1517, h1518, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1264, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1515, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1553_1, u0ehi4]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1515, h1517, h1518, hc45, hlam, hphi, ht23, ht34, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1515, h1517, h1518, hc45, hlam, hphi, ht23, ht34, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1515, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1262, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1512, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1518, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1549, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1263, hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1514, hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h0, h1260, h1263, h1517, h1518, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1551, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1553_1, u0ehi4]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1065, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1553_1, u0ehi0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1517, h1518, hc45, hlam, hphi, ht23, ht34, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1517, h1518, hc45, hlam, hphi, ht23, ht34, p1553_1, u2ehi3]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                          · linarith only [h1513, h1515, h1517, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h1260, h1263, h1514, h752, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h1513, h752, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1262, h1510, h1512, h752, hc02, hlam, hphi, u0ehi0]
                · linarith only [h0, h1511, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1510, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1585 | h1585
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1586 | h1586
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1587 | h1587
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1588 | h1588
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1589 | h1589
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1590 | h1590
                      · linarith only [h1263, h1586, h1590, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h1590, h752, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1589, h752, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h1261, h1588, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h1261, h1587, hlam]
              · linarith only [h0, h1260, h1586, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1597 | h1597
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1598 | h1598
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1599 | h1599
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1600 | h1600
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1601 | h1601
                      · linarith only [h1263, h1601, h752, hc13, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h1601, h752, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1600, h752, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h1262, h1599, hlam]
                · linarith only [h0, h1261, h1598, hlam]
              · linarith only [h0, h1260, h1597, hlam]
        · linarith only [h1260, h1262, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1260, h1261, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1610 | h1610
      · linarith only [h1260, h1610, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1612 | h1612
        · linarith only [h1260, h1612, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1614 | h1614
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1615 | h1615
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1616 | h1616
              · linarith only [h1260, h1616, hc12, hlam, hphi, ht01, u0ehi1]
              · linarith only [h0, h1616, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1619 | h1619
              · linarith only [h0, h1260, h1619, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h1619, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1622 | h1622
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1623 | h1623
              · linarith only [h0, h1260, h1623, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h1623, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1626 | h1626
              · linarith only [h0, h1260, h1626, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h1626, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 3258000 in
set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h752 | h752
  · exact r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h752
  · exact r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h752

set_option maxHeartbeats 3258000 in
set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_R_L_R_L_I_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
