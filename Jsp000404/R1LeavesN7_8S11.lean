import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 15198000 in
set_option maxHeartbeats 15198000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s1 m hb0 hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h6999 | h6999
    · rcases m.htr 0 1 5 (by decide) (by decide) with h7000 | h7000
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7001 | h7001
        · linarith only [h0, h1, h7001, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7003 | h7003
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7004 | h7004
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7005 | h7005
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7006 | h7006
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7007 | h7007
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7008 | h7008
                    · linarith only [h7001, h7003, h7007, h7008, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7010 | h7010
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7011 | h7011
                        · linarith only [h0, h1, h7011, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h0, h1, h7004, h7008, h7011, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h7003, h7008, h7010, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7015 | h7015
                    · linarith only [h0, h7001, h7004, h7015, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7017 | h7017
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7018 | h7018
                        · linarith only [h0, h1, h7015, h7018, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h7004, h7015, h7018, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h7003, h7015, h7017, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h7004, h7006, hlam]
              · linarith only [h1, h6999, h7005, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7024 | h7024
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7025 | h7025
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7026 | h7026
                  · linarith only [h7003, h7004, h7026, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7028 | h7028
                    · linarith only [h0, h1, h7001, h7028, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7030 | h7030
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7031 | h7031
                        · linarith only [h0, h1, h7004, h7028, h7031, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7033 | h7033
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7034 | h7034
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7035 | h7035
                              · linarith only [h1, h6999, h7026, h7035, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h7037 | h7037
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h7038 | h7038
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7039 | h7039
                                    · linarith only [h0, h6999, h7004, h7026, h7030, h7039, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7041 | h7041
                                      · linarith only [h1, h6999, h7028, h7030, h7037, h7039, h7041, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                                      · rcases h0bigk with h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c | h7043c
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h1, h7028, hc02, hc23, hlam, hphi, p7043_1]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h1, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          rcases p7043_3 (m.d 0 1) (by simp) with h7047 | h7047
                                          · rcases p7043_3 (m.d 0 2) (by simp) with h7048 | h7048
                                            · linarith only [h0, h7048, hlam]
                                            · linarith only [h7003, h7048, hlam]
                                          · linarith only [h6999, h7047, hlam]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h1, h7028, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7043_1, u5ehi0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h0, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7001, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h6999, h7004, h7039, hc14, hc45, hlam, hphi, p7043_1]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7004, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h0, h7030, h7037, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7043_1]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          rcases p7043_3 (m.d 0 1) (by simp) with h7059 | h7059
                                          · linarith only [h1, h7059, hlam]
                                          · linarith only [h0, h7059, hlam]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          rcases p7043_3 (m.d 0 1) (by simp) with h7063 | h7063
                                          · linarith only [h1, h7063, hlam]
                                          · linarith only [h6999, h7063, hlam]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          rcases p7043_3 (m.d 0 1) (by simp) with h7066 | h7066
                                          · linarith only [h1, h7066, hlam]
                                          · linarith only [h7000, h7066, hlam]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h6999, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7003, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7024, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7026, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7000, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h0, h1, h7000, h7028, h7030, h7037, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7043_1]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [h7025, hlam, p7043_0]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          rcases p7043_3 (m.d 0 1) (by simp) with h7077 | h7077
                                          · rcases p7043_3 (m.d 0 2) (by simp) with h7078 | h7078
                                            · linarith only [h7004, h7078, hlam]
                                            · linarith only [h7003, h7078, hlam]
                                          · linarith only [h6999, h7077, hlam]
                                        · have p7043_0 := h7043c.1
                                          have p7043_1 := h7043c.2.1
                                          have p7043_2 := h7043c.2.2.1
                                          have p7043_3 := h7043c.2.2.2
                                          linarith only [hlam, p7043_0]
                                  · linarith only [h0, h1, h7028, h7030, h7037, h7038, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1, h7000, h7028, h7037, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                            · linarith only [h1, h7000, h7030, h7031, h7034, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h7000, h7030, h7031, h7033, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h7003, h7028, h7030, hc12, hc23, hlam, hphi]
                · linarith only [h1, h7000, h7025, hlam]
              · linarith only [h1, h6999, h7024, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7090 | h7090
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7091 | h7091
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7092 | h7092
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7093 | h7093
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7094 | h7094
                    · linarith only [h7001, h7090, h7094, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7096 | h7096
                      · linarith only [h0, h7003, h7090, h7096, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7098 | h7098
                        · linarith only [h1, h6999, h7094, h7096, h7098, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h7003, h7090, h7098, hc12, hc24, hlam, hphi]
                  · linarith only [h7003, h7090, h7093, hlam]
                · linarith only [h1, h6999, h7003, h7090, h7092, hlam]
              · linarith only [h1, h6999, h7091, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7104 | h7104
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7105 | h7105
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7106 | h7106
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7107 | h7107
                    · linarith only [h0, h1, h7001, h7107, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7109 | h7109
                      · linarith only [h0, h1, h7003, h7106, h7107, h7109, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7111 | h7111
                        · linarith only [h0, h7090, h7111, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7113 | h7113
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7114 | h7114
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7115 | h7115
                              · linarith only [h1, h6999, h7107, h7115, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h1, h6999, h7106, h7107, h7109, h7115, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h6999, h7106, h7114, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h1, h6999, h7104, h7106, h7113, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7120 | h7120
                    · linarith only [h0, h1, h7001, h7120, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7122 | h7122
                      · linarith only [h0, h7003, h7122, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7124 | h7124
                        · linarith only [h0, h1, h7090, h7120, h7124, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7126 | h7126
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7127 | h7127
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7128 | h7128
                              · linarith only [h6999, h7106, h7128, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h7130 | h7130
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h7131 | h7131
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7132 | h7132
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7133 | h7133
                                      · linarith only [h6999, h7106, h7126, h7133, hlam]
                                      · rcases h0bigk with h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c | h7135c
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h0, h1, h7120, hc12, hc23, hlam, hphi, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h1, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h0, h1, h7003, h7120, hc12, hc23, hlam, hphi, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h1, h7120, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7135_1, u5ehi0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h0, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7001, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7003, hlam, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7090, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h0, h1, h7120, hc12, hc23, hlam, hphi, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          rcases p7135_3 (m.d 0 1) (by simp) with h7147 | h7147
                                          · linarith only [h1, h7147, hlam]
                                          · linarith only [h0, h7147, hlam]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          rcases p7135_3 (m.d 0 1) (by simp) with h7151 | h7151
                                          · linarith only [h1, h7151, hlam]
                                          · linarith only [h6999, h7151, hlam]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          rcases p7135_3 (m.d 0 1) (by simp) with h7154 | h7154
                                          · linarith only [h1, h7154, hlam]
                                          · linarith only [h7000, h7154, hlam]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h6999, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h0, h7106, h7132, hc12, hc24, hlam, hphi, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7104, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7106, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7000, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h0, h1, h7000, h7120, hc12, hc23, hlam, hphi, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h7105, hlam, p7135_0]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [h1, h6999, h7000, h7120, h7122, hc12, hc23, hlam, hphi, p7135_1]
                                        · have p7135_0 := h7135c.1
                                          have p7135_1 := h7135c.2.1
                                          have p7135_2 := h7135c.2.2.1
                                          have p7135_3 := h7135c.2.2.2
                                          linarith only [hlam, p7135_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7167 | h7167
                                      · linarith only [h0, h7003, h7132, h7167, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h0bigk with h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c | h7169c
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h0, h1, h7120, hc12, hc23, hlam, hphi, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h1, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h1, h6999, h7120, h7122, hc12, hc23, hlam, hphi, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h1, h7120, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7169_1, u5ehi0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h0, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7001, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7003, hlam, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7090, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h0, h1, h7120, hc12, hc23, hlam, hphi, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          rcases p7169_3 (m.d 0 1) (by simp) with h7181 | h7181
                                          · linarith only [h1, h7181, hlam]
                                          · linarith only [h0, h7181, hlam]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          rcases p7169_3 (m.d 0 1) (by simp) with h7185 | h7185
                                          · linarith only [h1, h7185, hlam]
                                          · linarith only [h6999, h7185, hlam]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          rcases p7169_3 (m.d 0 1) (by simp) with h7188 | h7188
                                          · linarith only [h1, h7188, hlam]
                                          · linarith only [h7000, h7188, hlam]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h6999, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h0, h1, h6999, h7120, hc12, hc23, hlam, hphi, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7104, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7106, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7000, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h0, h1, h7000, h7120, hc12, hc23, hlam, hphi, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h7105, hlam, p7169_0]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [h1, h6999, h7000, h7120, h7122, hc12, hc23, hlam, hphi, p7169_1]
                                        · have p7169_0 := h7169c.1
                                          have p7169_1 := h7169c.2.1
                                          have p7169_2 := h7169c.2.2.1
                                          have p7169_3 := h7169c.2.2.2
                                          linarith only [hlam, p7169_0]
                                  · linarith only [h0, h1, h7120, h7131, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h7000, h7120, h7126, h7128, h7130, hlam]
                            · linarith only [h1, h7000, h7127, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h7000, h7104, h7106, h7126, hlam]
                · linarith only [h1, h7000, h7105, hlam]
              · linarith only [h1, h6999, h7104, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7207 | h7207
        · linarith only [h0, h1, h7207, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7209 | h7209
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7210 | h7210
            · linarith only [h0, h7000, h7210, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7212 | h7212
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7213 | h7213
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7214 | h7214
                  · linarith only [h0, h7000, h7209, h7214, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7216 | h7216
                    · linarith only [h0, h7207, h7209, h7216, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7218 | h7218
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7219 | h7219
                        · linarith only [h0, h7000, h7210, h7219, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7221 | h7221
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7222 | h7222
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7223 | h7223
                              · linarith only [h6999, h7000, h7214, h7223, hlam]
                              · linarith only [h0, h7000, h7218, h7223, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h7218, h7222, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h7218, h7221, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h7209, h7216, h7218, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7229 | h7229
                  · linarith only [h0, h1, h7209, h7213, h7229, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7231 | h7231
                    · linarith only [h0, h1, h7213, h7231, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7233 | h7233
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7234 | h7234
                        · linarith only [h0, h1, h7213, h7234, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7236 | h7236
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7237 | h7237
                            · linarith only [h0, h1, h7213, h7233, h7237, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h1, h7233, h7237, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h7233, h7236, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h7207, h7209, h7233, hc12, hc23, hlam, hphi]
              · linarith only [h1, h6999, h7212, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7243 | h7243
            · linarith only [h6999, h7000, h7209, h7243, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7245 | h7245
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7246 | h7246
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7247 | h7247
                  · linarith only [h6999, h7000, h7247, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7249 | h7249
                    · linarith only [h0, h1, h7207, h7249, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7251 | h7251
                      · linarith only [h0, h1, h7209, h7251, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7253 | h7253
                        · linarith only [h0, h7000, h7243, h7253, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7255 | h7255
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7256 | h7256
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7257 | h7257
                              · linarith only [h6999, h7000, h7247, h7257, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h7259 | h7259
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h7260 | h7260
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7261 | h7261
                                    · linarith only [h6999, h7000, h7251, h7257, h7259, h7261, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7263 | h7263
                                      · linarith only [h6999, h7209, h7255, h7261, h7263, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h0bigk with h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h0, h7000, h7253, h7261, hc12, hc45, hlam, hphi, ht23, ht34, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h1, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7000, h7253, h7261, hc04, hc45, hlam, hphi, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7000, hlam, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h0, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7207, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7209, hlam, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7243, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h0, h7207, hc12, hc23, hlam, hphi, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          rcases p7265_3 (m.d 0 1) (by simp) with h7277 | h7277
                                          · linarith only [h1, h7277, hlam]
                                          · linarith only [h0, h7277, hlam]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          rcases p7265_3 (m.d 0 1) (by simp) with h7281 | h7281
                                          · linarith only [h1, h7281, hlam]
                                          · linarith only [h6999, h7281, hlam]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h1, h6999, h7000, h7249, h7251, hc12, hc23, hlam, hphi, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h6999, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h0, h1, h6999, h7249, hc12, hc23, hlam, hphi, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7245, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7247, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h0, h7000, h7253, h7261, hc12, hc45, hlam, hphi, ht23, ht34, p7265_1]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          rcases p7265_3 (m.d 0 1) (by simp) with h7291 | h7291
                                          · linarith only [h7000, h7291, hlam]
                                          · linarith only [h0, h7291, hlam]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [h7246, hlam, p7265_0]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          rcases p7265_3 (m.d 0 1) (by simp) with h7295 | h7295
                                          · linarith only [h7000, h7295, hlam]
                                          · linarith only [h6999, h7295, hlam]
                                        · have p7265_0 := h7265c.1
                                          have p7265_1 := h7265c.2.1
                                          have p7265_2 := h7265c.2.2.1
                                          have p7265_3 := h7265c.2.2.2
                                          linarith only [hlam, p7265_0]
                                  · linarith only [h1, h6999, h7249, h7251, h7260, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h6999, h7000, h7249, h7255, h7256, h7259, hlam]
                            · linarith only [h1, h6999, h7246, h7251, h7256, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h6999, h7251, h7255, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7303 | h7303
                  · linarith only [h6999, h7000, h7303, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7305 | h7305
                    · linarith only [h0, h1, h7246, h7305, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7307 | h7307
                      · linarith only [h0, h7209, h7307, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7309 | h7309
                        · linarith only [h1, h6999, h7246, h7307, h7309, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7311 | h7311
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7312 | h7312
                            · linarith only [h1, h6999, h7246, h7305, h7307, h7312, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h6999, h7307, h7312, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h6999, h7307, h7311, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h6999, h7245, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h7317 | h7317
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7318 | h7318
        · linarith only [h0, h1, h7318, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7320 | h7320
          · linarith only [h0, h6999, h7320, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7322 | h7322
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7323 | h7323
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7324 | h7324
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7325 | h7325
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7326 | h7326
                    · linarith only [h7318, h7322, h7326, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7328 | h7328
                      · linarith only [h0, h7320, h7322, h7328, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7330 | h7330
                        · linarith only [h0, h1, h7326, h7330, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h7322, h7326, h7330, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h6999, h7322, h7325, hlam]
                · linarith only [h0, h1, h7322, h7324, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7335 | h7335
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7336 | h7336
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7337 | h7337
                    · linarith only [h0, h1, h7323, h7337, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7339 | h7339
                      · linarith only [h0, h1, h7320, h7323, h7339, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7341 | h7341
                        · linarith only [h0, h1, h7323, h7341, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h1, h7322, h7323, h7341, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h7317, h7323, h7336, hlam]
                · linarith only [h0, h1, h7322, h7335, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7346 | h7346
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7347 | h7347
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7348 | h7348
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7349 | h7349
                    · linarith only [h0, h1, h7318, h7349, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7351 | h7351
                      · linarith only [h0, h1, h7320, h7348, h7349, h7351, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7353 | h7353
                        · linarith only [h0, h7322, h7353, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7355 | h7355
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7356 | h7356
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7357 | h7357
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h7358 | h7358
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h7359 | h7359
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7360 | h7360
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7361 | h7361
                                      · rcases h0bigk with h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h6999, h7349, h7355, hc02, hc23, hlam, hphi, p7362_1]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h1, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h6999, hlam, p7362_1]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h6999, h7349, h7355, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7362_1, u5ehi0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h0, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7318, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7320, hlam, p7362_1]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7322, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7317, hc03, hlam, hphi, ht0b, ht5b, p7362_1, u5ehi1]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          rcases p7362_3 (m.d 0 1) (by simp) with h7374 | h7374
                                          · linarith only [h1, h7374, hlam]
                                          · linarith only [h0, h7374, hlam]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h1, h6999, h7317, h7349, h7356, h7361, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7362_1, u5ehi4]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          rcases p7362_3 (m.d 0 1) (by simp) with h7379 | h7379
                                          · linarith only [h1, h7379, hlam]
                                          · linarith only [h7317, h7379, hlam]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7317, h7356, h7361, hc04, hlam, hphi, ht0b, ht5b, p7362_1, u5ehi4]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          rcases p7362_3 (m.d 0 1) (by simp) with h7383 | h7383
                                          · linarith only [h6999, h7383, hlam]
                                          · linarith only [h0, h7383, hlam]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7346, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          rcases p7362_3 (m.d 0 1) (by simp) with h7388 | h7388
                                          · linarith only [h6999, h7388, hlam]
                                          · linarith only [h7317, h7388, hlam]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7317, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h0, h1, h7317, h7349, hc12, hc23, hlam, hphi, p7362_1]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7347, hlam, p7362_0]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [h7348, hlam, p7362_1]
                                        · have p7362_0 := h7362c.1
                                          have p7362_1 := h7362c.2.1
                                          have p7362_2 := h7362c.2.2.1
                                          have p7362_3 := h7362c.2.2.2
                                          linarith only [hlam, p7362_0]
                                      · rcases h0bigk with h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c | h7396c
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h0, h6999, h7349, h7355, hc12, hc23, hlam, hphi, p7396_1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h1, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h6999, hlam, p7396_1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h6999, h7349, h7355, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7396_1, u5ehi0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h0, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7318, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7320, hlam, p7396_1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7322, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h0, h1, h7349, hc12, hc23, hlam, hphi, p7396_1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          rcases p7396_3 (m.d 0 1) (by simp) with h7408 | h7408
                                          · linarith only [h1, h7408, hlam]
                                          · linarith only [h0, h7408, hlam]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h1, h6999, h7317, h7349, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7396_1, u5ehi1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          rcases p7396_3 (m.d 0 1) (by simp) with h7413 | h7413
                                          · linarith only [h1, h7413, hlam]
                                          · linarith only [h7317, h7413, hlam]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7317, h7357, h7361, hc04, hlam, hphi, ht0b, ht5b, p7396_1, u5ehi3]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          rcases p7396_3 (m.d 0 1) (by simp) with h7417 | h7417
                                          · linarith only [h6999, h7417, hlam]
                                          · linarith only [h0, h7417, hlam]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7346, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          rcases p7396_3 (m.d 0 1) (by simp) with h7422 | h7422
                                          · linarith only [h6999, h7422, hlam]
                                          · linarith only [h7317, h7422, hlam]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7317, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h0, h1, h7317, h7349, hc12, hc23, hlam, hphi, p7396_1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7347, hlam, p7396_0]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [h7348, hlam, p7396_1]
                                        · have p7396_0 := h7396c.1
                                          have p7396_1 := h7396c.2.1
                                          have p7396_2 := h7396c.2.2.1
                                          have p7396_3 := h7396c.2.2.2
                                          linarith only [hlam, p7396_0]
                                    · linarith only [h0, h6999, h7351, h7360, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h6999, h7317, h7349, h7355, h7357, h7359, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · linarith only [h6999, h7317, h7349, h7355, h7357, h7358, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h6999, h7317, h7353, h7357, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h6999, h7317, h7355, h7356, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h7346, h7355, hlam]
                  · linarith only [h6999, h7317, h7348, hlam]
                · linarith only [h1, h7317, h7347, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7438 | h7438
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7439 | h7439
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7440 | h7440
                    · linarith only [h0, h1, h7346, h7440, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7442 | h7442
                      · linarith only [h0, h7320, h7442, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7444 | h7444
                        · linarith only [h0, h7322, h7444, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7446 | h7446
                          · linarith only [h7346, h7438, h7440, h7446, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · linarith only [h1, h7317, h7446, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                  · linarith only [h1, h7317, h7346, h7439, hlam]
                · linarith only [h1, h7317, h7438, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7451 | h7451
        · linarith only [h0, h1, h7451, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7453 | h7453
          · linarith only [h0, h6999, h7453, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7455 | h7455
            · linarith only [h0, h7317, h7455, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7457 | h7457
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7458 | h7458
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7459 | h7459
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7460 | h7460
                    · linarith only [h0, h1, h7451, h7460, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7462 | h7462
                      · linarith only [h0, h7317, h7453, h7459, h7462, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7464 | h7464
                        · linarith only [h0, h7317, h7455, h7464, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7466 | h7466
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7467 | h7467
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7468 | h7468
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h7469 | h7469
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h7470 | h7470
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7471 | h7471
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7472 | h7472
                                      · rcases h0bigk with h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7317, h7460, h7466, h7468, hc02, hc23, hlam, hphi, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h1, hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h6999, hlam, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7317, hlam, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h0, hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7451, hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7453, hlam, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7455, hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h0, h1, h7460, hc12, hc23, hlam, hphi, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          rcases p7473_3 (m.d 0 1) (by simp) with h7485 | h7485
                                          · linarith only [h1, h7485, hlam]
                                          · linarith only [h0, h7485, hlam]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h1, h7457, h7460, h7472, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7473_1, u5ehi4]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h0, h1, h7317, h7460, hc12, hc23, hlam, hphi, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h0, h6999, h7460, h7466, hc12, hc23, hlam, hphi, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          rcases p7473_3 (m.d 0 1) (by simp) with h7492 | h7492
                                          · linarith only [h6999, h7492, hlam]
                                          · linarith only [h0, h7492, hlam]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7457, hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h0, h6999, h7317, h7460, h7466, hc12, hc23, hlam, hphi, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h0, h7317, h7460, h7466, h7468, hc12, hc23, hlam, hphi, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          rcases p7473_3 (m.d 0 1) (by simp) with h7499 | h7499
                                          · linarith only [h7317, h7499, hlam]
                                          · linarith only [h0, h7499, hlam]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7458, hlam, p7473_0]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [h7459, hlam, p7473_1]
                                        · have p7473_0 := h7473c.1
                                          have p7473_1 := h7473c.2.1
                                          have p7473_2 := h7473c.2.2.1
                                          have p7473_3 := h7473c.2.2.2
                                          linarith only [hlam, p7473_0]
                                      · rcases h0bigk with h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, h1, h7460, hc12, hc23, hlam, hphi, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h1, hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h6999, hlam, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7317, hlam, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7451, hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7453, hlam, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7455, hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, h1, h7460, hc12, hc23, hlam, hphi, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          rcases p7505_3 (m.d 0 1) (by simp) with h7517 | h7517
                                          · linarith only [h1, h7517, hlam]
                                          · linarith only [h0, h7517, hlam]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h1, h7459, h7460, h7472, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, h1, h7317, h7460, hc12, hc23, hlam, hphi, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, h6999, h7460, h7466, hc12, hc23, hlam, hphi, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          rcases p7505_3 (m.d 0 1) (by simp) with h7524 | h7524
                                          · linarith only [h6999, h7524, hlam]
                                          · linarith only [h0, h7524, hlam]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7457, hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, h6999, h7317, h7460, h7466, hc12, hc23, hlam, hphi, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h0, h7317, h7460, h7466, h7468, hc12, hc23, hlam, hphi, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          rcases p7505_3 (m.d 0 1) (by simp) with h7531 | h7531
                                          · linarith only [h7317, h7531, hlam]
                                          · linarith only [h0, h7531, hlam]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7458, hlam, p7505_0]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [h7459, hlam, p7505_1]
                                        · have p7505_0 := h7505c.1
                                          have p7505_1 := h7505c.2.1
                                          have p7505_2 := h7505c.2.2.1
                                          have p7505_3 := h7505c.2.2.2
                                          linarith only [hlam, p7505_0]
                                    · linarith only [h0, h6999, h7462, h7471, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h0, h1, h7460, h7470, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h7317, h7460, h7466, h7468, h7469, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1, h6999, h7457, h7459, h7460, h7468, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h7458, h7467, hlam]
                          · linarith only [h1, h7457, h7466, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7543 | h7543
                    · linarith only [h0, h6999, h7459, h7543, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7545 | h7545
                      · linarith only [h0, h6999, h7459, h7545, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7547 | h7547
                        · linarith only [h0, h6999, h7459, h7547, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7549 | h7549
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7550 | h7550
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h7551 | h7551
                              · linarith only [h0, h6999, h7459, h7543, h7549, h7551, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h6999, h7551, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h7458, h7550, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h7549, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7556 | h7556
                  · linarith only [h7457, h7458, h7556, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7558 | h7558
                    · linarith only [h0, h1, h7458, h7558, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7560 | h7560
                      · linarith only [h0, h6999, h7556, h7560, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7562 | h7562
                        · linarith only [h0, h6999, h7455, h7457, h7458, h7562, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7564 | h7564
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h7565 | h7565
                            · linarith only [h0, h6999, h7457, h7458, h7558, h7565, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h7565, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h7457, h7564, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7569 | h7569
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7570 | h7570
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7571 | h7571
                    · linarith only [h0, h7451, h7571, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7573 | h7573
                      · linarith only [h0, h7453, h7573, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7575 | h7575
                        · linarith only [h0, h7317, h7455, h7575, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7577 | h7577
                          · linarith only [h0, h7317, h7457, h7569, h7571, h7577, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h7577, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h7457, h7569, h7570, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h7581 | h7581
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7582 | h7582
                    · linarith only [h0, h1, h7569, h7582, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7584 | h7584
                      · linarith only [h0, h7453, h7584, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7586 | h7586
                        · linarith only [h0, h1, h7569, h7586, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7588 | h7588
                          · linarith only [h0, h1, h7457, h7582, h7588, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h7588, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h7591 | h7591
                    · linarith only [h0, h1, h7569, h7591, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h7593 | h7593
                      · linarith only [h0, h1, h7457, h7581, h7593, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h7595 | h7595
                        · linarith only [h0, h1, h7457, h7581, h7595, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h7597 | h7597
                          · linarith only [h0, h1, h7457, h7591, h7597, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h7597, hc12, hc34, hlam, hphi, ht23]

end R2N4
