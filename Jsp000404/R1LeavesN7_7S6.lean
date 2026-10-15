import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3894 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h3981 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h3982 | h3982
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3983 | h3983
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3984 | h3984
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3985 | h3985
        · linarith only [h1, h3985, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3987 | h3987
          · linarith only [h1, h3894, h3987, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3989 | h3989
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3990 | h3990
              · linarith only [h0, h2, h3989, h3990, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3992 | h3992
                · linarith only [h1, h3894, h3982, h3992, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3994 | h3994
                  · linarith only [h0, h3983, h3994, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3996 | h3996
                    · rcases h1bigk with h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3983, h3989, h3990, h3994, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        rcases p3997_3 (m.d 0 1) (by simp) with h4000 | h4000
                        · rcases p3997_3 (m.d 1 2) (by simp) with h4001 | h4001
                          · linarith only [h0, h4001, hlam]
                          · linarith only [h3982, h4001, hlam]
                        · linarith only [h4000, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3989, h3990, h3994, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        rcases p3997_3 (m.d 0 1) (by simp) with h4006 | h4006
                        · rcases p3997_3 (m.d 1 2) (by simp) with h4007 | h4007
                          · linarith only [h0, h4007, hlam]
                          · linarith only [h3984, h4007, hlam]
                        · linarith only [h4006, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h0, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        rcases p3997_3 (m.d 0 1) (by simp) with h4013 | h4013
                        · rcases p3997_3 (m.d 1 2) (by simp) with h4014 | h4014
                          · rcases p3997_3 (m.d 1 3) (by simp) with h4015 | h4015
                            · linarith only [h3982, h4015, hlam]
                            · rcases p3997_3 (m.d 1 4) (by simp) with h4017 | h4017
                              · linarith only [h3983, h4017, hlam]
                              · linarith only [h3985, h4017, hlam]
                          · linarith only [h3982, h4014, hlam]
                        · linarith only [h1, h4013, hlam]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h0, h3989, h3990, h3994, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h0, h3989, h3990, h3994, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h1, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3982, hlam, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3985, hlam, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3987, hlam, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h2, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3983, hlam, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        rcases p3997_3 (m.d 0 1) (by simp) with h4031 | h4031
                        · rcases p3997_3 (m.d 1 2) (by simp) with h4032 | h4032
                          · rcases p3997_3 (m.d 1 3) (by simp) with h4033 | h4033
                            · linarith only [h3985, h4033, hlam]
                            · rcases p3997_3 (m.d 1 4) (by simp) with h4035 | h4035
                              · rcases p3997_3 (m.d 1 5) (by simp) with h4036 | h4036
                                · linarith only [h3989, h4036, hlam]
                                · linarith only [h3987, h4036, hlam]
                              · linarith only [h3985, h4035, hlam]
                          · linarith only [h3982, h4032, hlam]
                        · linarith only [h1, h4031, hlam]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h2, h3989, h3990, h3994, h7, hc23, hc34, hlam, hphi, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3984, hlam, p3997_1]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        rcases p3997_3 (m.d 0 1) (by simp) with h4046 | h4046
                        · rcases p3997_3 (m.d 1 2) (by simp) with h4047 | h4047
                          · rcases p3997_3 (m.d 1 3) (by simp) with h4048 | h4048
                            · linarith only [h3987, h4048, hlam]
                            · rcases p3997_3 (m.d 1 4) (by simp) with h4050 | h4050
                              · rcases p3997_3 (m.d 1 5) (by simp) with h4051 | h4051
                                · rcases h1emax with h4052 | h4052 | h4052 | h4052 | h4052
                                  · linarith only [h3, h3982, h4052, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3997_1]
                                  · linarith only [h3982, h3983, h3989, h4052, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3997_1]
                                  · rcases h3bigk with h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3894, h3982, h3996, hc23, hc34, hlam, hphi, p4055_1]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3894, h3996, hc23, hc34, hlam, hphi, p4055_1]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h7, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3894, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h1, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h0, h3983, h3989, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3997_1, p4055_1]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3985, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3987, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h4, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3982, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3990, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3992, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      rcases p4055_3 (m.d 0 3) (by simp) with h4071 | h4071
                                      · linarith only [h4071, hlam, p4055_0]
                                      · rcases p4055_3 (m.d 1 3) (by simp) with h4073 | h4073
                                        · linarith only [h3985, h4073, hlam]
                                        · rcases p4055_3 (m.d 2 3) (by simp) with h4075 | h4075
                                          · linarith only [h3990, h4075, hlam]
                                          · rcases p4055_3 (m.d 3 4) (by simp) with h4077 | h4077
                                            · rcases p4055_3 (m.d 3 5) (by simp) with h4078 | h4078
                                              · linarith only [h3996, h4078, hlam]
                                              · linarith only [h3894, h4078, hlam]
                                            · linarith only [h4077, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      rcases p4055_3 (m.d 0 3) (by simp) with h4082 | h4082
                                      · linarith only [h4082, h7, hlam]
                                      · linarith only [h1, h4082, hlam]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      rcases p4055_3 (m.d 0 3) (by simp) with h4085 | h4085
                                      · linarith only [h4085, h7, hlam]
                                      · linarith only [h4, h4085, hlam]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3894, hc03, hc34, hlam, hphi, p4055_1]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      rcases p4055_3 (m.d 0 3) (by simp) with h4090 | h4090
                                      · linarith only [h4090, hlam, p4055_0]
                                      · rcases p4055_3 (m.d 1 3) (by simp) with h4092 | h4092
                                        · linarith only [h3987, h4092, hlam]
                                        · rcases p4055_3 (m.d 2 3) (by simp) with h4094 | h4094
                                          · linarith only [h3992, h4094, hlam]
                                          · rcases p4055_3 (m.d 3 4) (by simp) with h4096 | h4096
                                            · rcases p4055_3 (m.d 3 5) (by simp) with h4097 | h4097
                                              · rcases h5bigk with h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c | h4098c
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3981, h3982, h7, hc23, hc34, hlam, hphi, p3997_1, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  rcases p4098_3 (m.d 0 5) (by simp) with h4101 | h4101
                                                  · rcases p4098_3 (m.d 1 5) (by simp) with h4102 | h4102
                                                    · linarith only [h3, h4102, hlam]
                                                    · linarith only [h3984, h4102, hlam]
                                                  · linarith only [h4101, h6, hlam]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3894, hlam, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3981, h3990, h3994, h7, hc23, hc34, hlam, hphi, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3, hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p4098_1, u5ehi2]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3987, hlam, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h0, h3983, h3989, h3990, h3994, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h6, hlam, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3984, hlam, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3992, hlam, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3994, hlam, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3981, h3990, h3994, h3996, hc23, hc34, hlam, hphi, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3982, h3996, hc23, hc34, hlam, hphi, p3997_1, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  rcases p4098_3 (m.d 0 5) (by simp) with h4120 | h4120
                                                  · linarith only [h3894, h4120, hlam]
                                                  · linarith only [h4120, h6, hlam]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3990, h3994, h3996, hc23, hc34, hlam, hphi, p4098_1]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3981, hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3989, hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3981, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4098_1, u5ehi2]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [h3996, hlam, p4098_0]
                                                · have p4098_0 := h4098c.1
                                                  have p4098_1 := h4098c.2.1
                                                  have p4098_2 := h4098c.2.2.1
                                                  have p4098_3 := h4098c.2.2.2
                                                  linarith only [hlam, p4098_0]
                                              · linarith only [h4097, hlam, p4055_0]
                                            · linarith only [h4096, h7, hlam]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      rcases p4055_3 (m.d 0 3) (by simp) with h4132 | h4132
                                      · linarith only [h3894, h4132, hlam]
                                      · linarith only [h1, h4132, hlam]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      rcases p4055_3 (m.d 0 3) (by simp) with h4135 | h4135
                                      · linarith only [h3894, h4135, hlam]
                                      · linarith only [h4, h4135, hlam]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [h3996, hlam, p4055_0]
                                    · have p4055_0 := h4055c.1
                                      have p4055_1 := h4055c.2.1
                                      have p4055_2 := h4055c.2.2.1
                                      have p4055_3 := h4055c.2.2.2
                                      linarith only [hlam, p4055_0]
                                  · linarith only [h3982, h3989, h4052, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3997_1]
                                  · linarith only [h3982, h4052, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3997_1]
                                · linarith only [h3987, h4051, hlam]
                              · linarith only [h3985, h4050, hlam]
                          · linarith only [h3982, h4047, hlam]
                        · linarith only [h1, h4046, hlam]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [h3989, hlam, p3997_0]
                      · have p3997_0 := h3997c.1
                        have p3997_1 := h3997c.2.1
                        have p3997_2 := h3997c.2.2.1
                        have p3997_3 := h3997c.2.2.2
                        linarith only [hlam, p3997_0]
                    · linarith only [h2, h3989, h3996, h7, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4149 | h4149
              · linarith only [h3981, h3982, h3985, h3989, h4149, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4151 | h4151
                · linarith only [h3981, h3982, h3985, h3989, h4151, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4153 | h4153
                  · linarith only [h0, h3983, h3985, h3989, h4153, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4155 | h4155
                    · rcases h1bigk with h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3984, hc01, hlam, hphi, ht0b, ht5b, p4156_1, u5ehi2]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        rcases p4156_3 (m.d 0 1) (by simp) with h4159 | h4159
                        · rcases p4156_3 (m.d 1 2) (by simp) with h4160 | h4160
                          · linarith only [h0, h4160, hlam]
                          · linarith only [h3982, h4160, hlam]
                        · linarith only [h4159, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        rcases p4156_3 (m.d 0 1) (by simp) with h4164 | h4164
                        · rcases p4156_3 (m.d 1 2) (by simp) with h4165 | h4165
                          · linarith only [h0, h4165, hlam]
                          · linarith only [h3983, h4165, hlam]
                        · linarith only [h4164, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        rcases p4156_3 (m.d 0 1) (by simp) with h4169 | h4169
                        · rcases p4156_3 (m.d 1 2) (by simp) with h4170 | h4170
                          · linarith only [h0, h4170, hlam]
                          · linarith only [h3984, h4170, hlam]
                        · linarith only [h4169, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h0, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        rcases p4156_3 (m.d 0 1) (by simp) with h4176 | h4176
                        · rcases p4156_3 (m.d 1 2) (by simp) with h4177 | h4177
                          · rcases p4156_3 (m.d 1 3) (by simp) with h4178 | h4178
                            · linarith only [h3982, h4178, hlam]
                            · rcases p4156_3 (m.d 1 4) (by simp) with h4180 | h4180
                              · linarith only [h3983, h4180, hlam]
                              · linarith only [h3985, h4180, hlam]
                          · linarith only [h3982, h4177, hlam]
                        · linarith only [h1, h4176, hlam]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        rcases p4156_3 (m.d 0 1) (by simp) with h4185 | h4185
                        · rcases p4156_3 (m.d 1 2) (by simp) with h4186 | h4186
                          · rcases p4156_3 (m.d 1 3) (by simp) with h4187 | h4187
                            · linarith only [h3982, h4187, hlam]
                            · rcases p4156_3 (m.d 1 4) (by simp) with h4189 | h4189
                              · linarith only [h3983, h4189, hlam]
                              · rcases p4156_3 (m.d 1 5) (by simp) with h4191 | h4191
                                · linarith only [h3984, h4191, hlam]
                                · linarith only [h3989, h4191, hlam]
                          · linarith only [h3983, h4186, hlam]
                        · linarith only [h2, h4185, hlam]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p4156_1, u5ehi1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h1, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3982, hlam, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3985, hlam, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3987, hlam, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h2, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3983, hlam, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3981, h3989, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3989, hlam, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3, hlam, p4156_0]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3984, hlam, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3981, h3982, h3989, h7, hc23, hc34, hlam, hphi, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [h3981, h3982, h3985, h3989, h7, hc23, hc34, hlam, hphi, p4156_1]
                      · have p4156_0 := h4156c.1
                        have p4156_1 := h4156c.2.1
                        have p4156_2 := h4156c.2.2.1
                        have p4156_3 := h4156c.2.2.2
                        linarith only [hlam, p4156_0]
                    · linarith only [h3981, h4155, h7, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4213 | h4213
        · linarith only [h1, h3981, h4213, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4215 | h4215
          · linarith only [h1, h3894, h4215, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4217 | h4217
            · linarith only [h0, h3983, h3984, h4217, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4219 | h4219
              · linarith only [h1, h3981, h3982, h4217, h4219, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4221 | h4221
                · linarith only [h1, h3894, h3982, h4221, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4223 | h4223
                  · linarith only [h3983, h3984, h4217, h4223, hlam]
                  · linarith only [h3981, h3983, h3984, h4219, h4223, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4226 | h4226
      · linarith only [h0, h3983, h4226, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4228 | h4228
        · linarith only [h1, h4228, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4230 | h4230
          · linarith only [h3894, h3981, h3982, h4226, h4230, h6, h7, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4232 | h4232
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4233 | h4233
              · linarith only [h1, h2, h3982, h4232, h4233, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4235 | h4235
                · linarith only [h0, h3894, h3982, h4226, h4235, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4237 | h4237
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4238 | h4238
                    · rcases h1bigk with h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c | h4239c
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        rcases p4239_3 (m.d 0 1) (by simp) with h4241 | h4241
                        · rcases p4239_3 (m.d 1 2) (by simp) with h4242 | h4242
                          · linarith only [h4242, hlam, p4239_0]
                          · rcases p4239_3 (m.d 1 3) (by simp) with h4244 | h4244
                            · linarith only [h1, h4244, hlam]
                            · rcases p4239_3 (m.d 1 4) (by simp) with h4246 | h4246
                              · linarith only [h2, h4246, hlam]
                              · linarith only [h3983, h4246, hlam]
                        · linarith only [h4241, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        rcases p4239_3 (m.d 0 1) (by simp) with h4250 | h4250
                        · rcases p4239_3 (m.d 1 2) (by simp) with h4251 | h4251
                          · linarith only [h0, h4251, hlam]
                          · linarith only [h3982, h4251, hlam]
                        · linarith only [h4250, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h4232, hc01, hlam, hphi, ht0b, ht5b, p4239_1, u5ehi4]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        rcases p4239_3 (m.d 0 1) (by simp) with h4256 | h4256
                        · rcases p4239_3 (m.d 1 2) (by simp) with h4257 | h4257
                          · linarith only [h0, h4257, hlam]
                          · rcases p4239_3 (m.d 1 3) (by simp) with h4259 | h4259
                            · linarith only [h1, h4259, hlam]
                            · rcases p4239_3 (m.d 1 4) (by simp) with h4261 | h4261
                              · linarith only [h2, h4261, hlam]
                              · linarith only [h4232, h4261, hlam]
                        · linarith only [h4256, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h0, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h0, h4226, h4237, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4239_1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h3983, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h4226, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h1, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h3982, hlam, p4239_1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h4228, hlam, p4239_1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h4230, hlam, p4239_1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h2, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h2, h3982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4239_1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        rcases p4239_3 (m.d 0 1) (by simp) with h4277 | h4277
                        · rcases p4239_3 (m.d 1 2) (by simp) with h4278 | h4278
                          · linarith only [h3983, h4278, hlam]
                          · linarith only [h3982, h4278, hlam]
                        · linarith only [h1, h4277, hlam]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h0, h3983, h5, hc01, hlam, hphi, ht0b, ht5b, p4239_1, u5ehi1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h3, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h3, h3982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4239_1]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        rcases p4239_3 (m.d 0 1) (by simp) with h4286 | h4286
                        · rcases p4239_3 (m.d 1 2) (by simp) with h4287 | h4287
                          · linarith only [h4226, h4287, hlam]
                          · linarith only [h3982, h4287, hlam]
                        · linarith only [h1, h4286, hlam]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [h4232, hlam, p4239_0]
                      · have p4239_0 := h4239c.1
                        have p4239_1 := h4239c.2.1
                        have p4239_2 := h4239c.2.2.1
                        have p4239_3 := h4239c.2.2.2
                        linarith only [hlam, p4239_0]
                    · linarith only [h3981, h4238, h7, hlam]
                  · linarith only [h3983, h4232, h4237, hlam]
            · linarith only [h3981, h3982, h3983, h4232, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4296 | h4296
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4297 | h4297
      · linarith only [h3982, h4, h4297, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4299 | h4299
        · linarith only [h3982, h4, h4299, h7, hlam]
        · linarith only [h3982, h4296, h4299, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4302 | h4302
      · linarith only [h3982, h4, h4302, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4304 | h4304
        · linarith only [h1, h3982, h4, h4304, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4306 | h4306
          · linarith only [h1, h3894, h3982, h4, h4306, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4308 | h4308
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4309 | h4309
              · linarith only [h4, h4309, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4311 | h4311
                · linarith only [h3894, h4, h4311, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4313 | h4313
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4314 | h4314
                    · rcases h1bigk with h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c | h4315c
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4317 | h4317
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4318 | h4318
                          · linarith only [h4318, hlam, p4315_0]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4320 | h4320
                            · linarith only [h1, h4320, hlam]
                            · linarith only [h3982, h4320, hlam]
                        · linarith only [h4317, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4324 | h4324
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4325 | h4325
                          · linarith only [h0, h4325, hlam]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4327 | h4327
                            · linarith only [h4327, hlam, p4315_0]
                            · rcases p4315_3 (m.d 1 4) (by simp) with h4329 | h4329
                              · linarith only [h2, h4329, hlam]
                              · linarith only [h4304, h4329, hlam]
                        · linarith only [h4324, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h4308, hc01, hlam, hphi, ht0b, ht5b, p4315_1, u5ehi4]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4334 | h4334
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4335 | h4335
                          · linarith only [h0, h4335, hlam]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4337 | h4337
                            · linarith only [h1, h4337, hlam]
                            · rcases p4315_3 (m.d 1 4) (by simp) with h4339 | h4339
                              · linarith only [h2, h4339, hlam]
                              · linarith only [h4308, h4339, hlam]
                        · linarith only [h4334, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h0, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h3982, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h4296, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h4302, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h1, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h3894, h3982, h4, h4314, hc12, hc34, hlam, hphi, ht23, p4315_1]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h4304, hlam, p4315_1]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h4306, hlam, p4315_1]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h2, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4354 | h4354
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4355 | h4355
                          · linarith only [h4296, h4355, hlam]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4357 | h4357
                            · linarith only [h4304, h4357, hlam]
                            · linarith only [h3982, h4357, hlam]
                        · linarith only [h0, h4354, hlam]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4361 | h4361
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4362 | h4362
                          · linarith only [h4296, h4362, hlam]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4364 | h4364
                            · linarith only [h4304, h4364, hlam]
                            · rcases p4315_3 (m.d 1 4) (by simp) with h4366 | h4366
                              · rcases p4315_3 (m.d 1 5) (by simp) with h4367 | h4367
                                · linarith only [h4308, h4367, hlam]
                                · linarith only [h4306, h4367, hlam]
                              · linarith only [h4304, h4366, hlam]
                        · linarith only [h1, h4361, hlam]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h0, h4296, h4308, h5, hc01, hlam, hphi, ht0b, ht5b, p4315_1, u5ehi4]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h3, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4375 | h4375
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4376 | h4376
                          · linarith only [h4302, h4376, hlam]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4378 | h4378
                            · linarith only [h4306, h4378, hlam]
                            · linarith only [h3982, h4378, hlam]
                        · linarith only [h0, h4375, hlam]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        rcases p4315_3 (m.d 0 1) (by simp) with h4382 | h4382
                        · rcases p4315_3 (m.d 1 2) (by simp) with h4383 | h4383
                          · linarith only [h4302, h4383, hlam]
                          · rcases p4315_3 (m.d 1 3) (by simp) with h4385 | h4385
                            · linarith only [h4306, h4385, hlam]
                            · rcases p4315_3 (m.d 1 4) (by simp) with h4387 | h4387
                              · rcases p4315_3 (m.d 1 5) (by simp) with h4388 | h4388
                                · rcases h1emax with h4389 | h4389 | h4389 | h4389 | h4389
                                  · linarith only [h0, h3982, h4296, h4308, h4389, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4315_1]
                                  · rcases h3bigk with h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3894, h3982, h4314, hc12, hc34, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3894, h4314, hc23, hc34, hlam, hphi, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h7, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3894, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h1, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3982, hlam, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h4304, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h4306, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h4, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3894, h3982, h4, h4314, hc12, hc34, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h4309, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h4311, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3982, h4, hc12, hc34, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      rcases p4391_3 (m.d 0 3) (by simp) with h4408 | h4408
                                      · linarith only [h4408, h7, hlam]
                                      · linarith only [h1, h4408, hlam]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3982, hc12, hc34, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3894, h3982, h4, hc12, hc34, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3982, h4, hc12, hc35, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      rcases p4391_3 (m.d 0 3) (by simp) with h4415 | h4415
                                      · linarith only [h3894, h4415, hlam]
                                      · linarith only [h1, h4415, hlam]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h3982, h4314, hc12, hc34, hlam, hphi, ht23, p4391_1]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [h4314, hlam, p4391_0]
                                    · have p4391_0 := h4391c.1
                                      have p4391_1 := h4391c.2.1
                                      have p4391_2 := h4391c.2.2.1
                                      have p4391_3 := h4391c.2.2.2
                                      linarith only [hlam, p4391_0]
                                  · rcases h3bigk with h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h7, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3894, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h1, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, hlam, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h4304, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h4306, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h4, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3894, h3982, h4, h4314, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h4309, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h4311, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, h4, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      rcases p4421_3 (m.d 0 3) (by simp) with h4438 | h4438
                                      · linarith only [h4438, h7, hlam]
                                      · linarith only [h1, h4438, hlam]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3894, h3982, h4, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, h4, hc12, hc35, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      rcases p4421_3 (m.d 0 3) (by simp) with h4445 | h4445
                                      · linarith only [h3894, h4445, hlam]
                                      · linarith only [h1, h4445, hlam]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h3982, h4314, hc12, hc34, hlam, hphi, ht23, p4421_1]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [h4314, hlam, p4421_0]
                                    · have p4421_0 := h4421c.1
                                      have p4421_1 := h4421c.2.1
                                      have p4421_2 := h4421c.2.2.1
                                      have p4421_3 := h4421c.2.2.2
                                      linarith only [hlam, p4421_0]
                                  · linarith only [h3982, h4308, h4389, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4315_1]
                                  · linarith only [h3982, h4389, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4315_1]
                                · linarith only [h4306, h4388, hlam]
                              · linarith only [h4304, h4387, hlam]
                        · linarith only [h1, h4382, hlam]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [h4308, hlam, p4315_0]
                      · have p4315_0 := h4315c.1
                        have p4315_1 := h4315c.2.1
                        have p4315_2 := h4315c.2.2.1
                        have p4315_3 := h4315c.2.2.2
                        linarith only [hlam, p4315_0]
                    · linarith only [h3982, h4, h4314, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h4296, h4308, h4313, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4460 | h4460
              · linarith only [h3981, h3982, h4304, h4308, h4460, h7, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4462 | h4462
                · linarith only [h3894, h4, h4462, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4464 | h4464
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4465 | h4465
                    · rcases h1bigk with h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h3982, h4304, h4308, h4464, h5, hlam, p4466_2]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4304, h4308, h4464, h5, hlam, p4466_2]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4308, h4464, h5, hlam, p4466_2]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        rcases p4466_3 (m.d 0 1) (by simp) with h4471 | h4471
                        · rcases p4466_3 (m.d 1 2) (by simp) with h4472 | h4472
                          · linarith only [h0, h4472, hlam]
                          · rcases p4466_3 (m.d 1 3) (by simp) with h4474 | h4474
                            · linarith only [h1, h4474, hlam]
                            · rcases p4466_3 (m.d 1 4) (by simp) with h4476 | h4476
                              · linarith only [h2, h4476, hlam]
                              · rcases p4466_3 (m.d 1 5) (by simp) with h4478 | h4478
                                · linarith only [h4478, hlam, p4466_0]
                                · rcases h1emax with h4480 | h4480 | h4480 | h4480 | h4480
                                  · linarith only [h0, h3982, h4304, h4308, h4464, h4480, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h3bigk with h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c | h4482c
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3894, h3982, h4465, hc12, hc34, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3894, h4465, hc23, hc34, hlam, hphi, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h7, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3894, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h1, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3982, hlam, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h4304, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h4306, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h4, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3894, h3982, h4, h4465, hc12, hc34, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h4460, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h4462, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3982, h4, hc12, hc34, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      rcases p4482_3 (m.d 0 3) (by simp) with h4499 | h4499
                                      · linarith only [h4499, h7, hlam]
                                      · linarith only [h1, h4499, hlam]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3982, hc12, hc34, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3894, h3982, h4, hc12, hc34, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3982, h4, hc12, hc35, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      rcases p4482_3 (m.d 0 3) (by simp) with h4506 | h4506
                                      · linarith only [h3894, h4506, hlam]
                                      · linarith only [h1, h4506, hlam]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h3982, h4465, hc12, hc34, hlam, hphi, ht23, p4482_1]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [h4465, hlam, p4482_0]
                                    · have p4482_0 := h4482c.1
                                      have p4482_1 := h4482c.2.1
                                      have p4482_2 := h4482c.2.2.1
                                      have p4482_3 := h4482c.2.2.2
                                      linarith only [hlam, p4482_0]
                                  · rcases h3bigk with h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h7, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3894, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h1, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, hlam, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h4304, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h4306, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h4, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3894, h3982, h4, h4465, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h4460, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h4462, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, h4, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      rcases p4512_3 (m.d 0 3) (by simp) with h4529 | h4529
                                      · linarith only [h4529, h7, hlam]
                                      · linarith only [h1, h4529, hlam]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3894, h3982, h4, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, h4, hc12, hc35, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      rcases p4512_3 (m.d 0 3) (by simp) with h4536 | h4536
                                      · linarith only [h3894, h4536, hlam]
                                      · linarith only [h1, h4536, hlam]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h3982, h4465, hc12, hc34, hlam, hphi, ht23, p4512_1]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [h4465, hlam, p4512_0]
                                    · have p4512_0 := h4512c.1
                                      have p4512_1 := h4512c.2.1
                                      have p4512_2 := h4512c.2.2.1
                                      have p4512_3 := h4512c.2.2.2
                                      linarith only [hlam, p4512_0]
                                  · rcases h3bigk with h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h7, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3894, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h1, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, hlam, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h4304, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h4306, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h4, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, h4, h7, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h4460, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h4462, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, h4, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      rcases p4542_3 (m.d 0 3) (by simp) with h4559 | h4559
                                      · linarith only [h4559, h7, hlam]
                                      · linarith only [h1, h4559, hlam]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3894, h3982, h4, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, h4, hc12, hc35, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      rcases p4542_3 (m.d 0 3) (by simp) with h4566 | h4566
                                      · linarith only [h3894, h4566, hlam]
                                      · linarith only [h1, h4566, hlam]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h3982, h4465, hc12, hc34, hlam, hphi, ht23, p4542_1]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [h4465, hlam, p4542_0]
                                    · have p4542_0 := h4542c.1
                                      have p4542_1 := h4542c.2.1
                                      have p4542_2 := h4542c.2.2.1
                                      have p4542_3 := h4542c.2.2.2
                                      linarith only [hlam, p4542_0]
                                  · rcases h3bigk with h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, h7, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h7, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3894, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h1, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, hlam, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h4304, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h4306, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h4, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3894, h3982, h4, h4465, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h4460, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h4462, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, h4, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      rcases p4572_3 (m.d 0 3) (by simp) with h4589 | h4589
                                      · linarith only [h4589, h7, hlam]
                                      · linarith only [h1, h4589, hlam]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3894, h3982, h4, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, h4, hc12, hc35, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      rcases p4572_3 (m.d 0 3) (by simp) with h4596 | h4596
                                      · linarith only [h3894, h4596, hlam]
                                      · linarith only [h1, h4596, hlam]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h3982, h4465, hc12, hc34, hlam, hphi, ht23, p4572_1]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [h4465, hlam, p4572_0]
                                    · have p4572_0 := h4572c.1
                                      have p4572_1 := h4572c.2.1
                                      have p4572_2 := h4572c.2.2.1
                                      have p4572_3 := h4572c.2.2.2
                                      linarith only [hlam, p4572_0]
                        · linarith only [h4471, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h3982, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h4296, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h4302, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h1, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4304, h4308, h4464, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h4304, hlam, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h4306, hlam, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h2, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4308, h4464, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4308, h4464, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h4308, hlam, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h3, hlam, p4466_0]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4308, h4464, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h3982, h4308, h4464, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [h0, h4308, h4464, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4466_1]
                      · have p4466_0 := h4466c.1
                        have p4466_1 := h4466c.2.1
                        have p4466_2 := h4466c.2.2.1
                        have p4466_3 := h4466c.2.2.2
                        linarith only [hlam, p4466_0]
                    · linarith only [h0, h3982, h4, h4464, h4465, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h3981, h4296, h4464, h7, hc12, hc34, hlam, hphi, ht23]

end R2N4
