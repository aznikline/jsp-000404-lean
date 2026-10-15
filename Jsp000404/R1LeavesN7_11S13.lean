import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S11
import Jsp000404.R1LeavesN7_11S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 15178000 in
set_option maxHeartbeats 15178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6383 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 5 (by decide) (by decide) with h7023 | h7023
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7024 | h7024
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7025 | h7025
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7026 | h7026
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7027 | h7027
          · linarith only [h0, h3, h7027, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7029 | h7029
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7030 | h7030
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7031 | h7031
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7032 | h7032
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7033 | h7033
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7034 | h7034
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7035 | h7035
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7036 | h7036
                          · rcases h2bigk with h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h6383, h7029, h7033, h7034, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h3, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h6383, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              rcases p7037_3 (m.d 0 2) (by simp) with h7042 | h7042
                              · rcases p7037_3 (m.d 1 2) (by simp) with h7043 | h7043
                                · linarith only [h0, h7043, hlam]
                                · linarith only [h7029, h7043, hlam]
                              · linarith only [h7042, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h0, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7027, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h6383, hc12, hlam, hphi, ht01, p7037_1, u0ehi1]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              rcases p7037_3 (m.d 0 2) (by simp) with h7051 | h7051
                              · rcases p7037_3 (m.d 1 2) (by simp) with h7052 | h7052
                                · rcases p7037_3 (m.d 2 3) (by simp) with h7053 | h7053
                                  · rcases p7037_3 (m.d 2 4) (by simp) with h7054 | h7054
                                    · rcases p7037_3 (m.d 2 5) (by simp) with h7055 | h7055
                                      · linarith only [h7055, hlam, p7037_0]
                                      · rcases h3bigk with h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c | h7057c
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h3, h7027, h7034, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1, p7057_1]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h3, hlam, p7057_1]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          rcases p7057_3 (m.d 0 3) (by simp) with h7061 | h7061
                                          · rcases p7057_3 (m.d 1 3) (by simp) with h7062 | h7062
                                            · linarith only [h1, h7062, hlam]
                                            · linarith only [h7030, h7062, hlam]
                                          · linarith only [h7061, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          rcases p7057_3 (m.d 0 3) (by simp) with h7066 | h7066
                                          · rcases p7057_3 (m.d 1 3) (by simp) with h7067 | h7067
                                            · linarith only [h1, h7067, hlam]
                                            · linarith only [h7031, h7067, hlam]
                                          · linarith only [h7066, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h1, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7027, hlam, p7057_1]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h1, h7036, hc01, hc45, hlam, hphi, ht0b, ht5b, p7057_1]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          rcases p7057_3 (m.d 0 3) (by simp) with h7075 | h7075
                                          · rcases p7057_3 (m.d 1 3) (by simp) with h7076 | h7076
                                            · rcases p7057_3 (m.d 2 3) (by simp) with h7077 | h7077
                                              · rcases p7057_3 (m.d 3 4) (by simp) with h7078 | h7078
                                                · linarith only [h7030, h7078, hlam]
                                                · linarith only [h7036, h7078, hlam]
                                              · linarith only [h7034, h7077, hlam]
                                            · linarith only [h7076, hlam, p7057_0]
                                          · linarith only [h7025, h7075, hlam]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p7057_1, u0ehi2]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7027, h7034, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1, p7057_1]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          rcases p7057_3 (m.d 0 3) (by simp) with h7087 | h7087
                                          · linarith only [h3, h7087, hlam]
                                          · linarith only [h7024, h7087, hlam]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h0, h3, h7034, hlam, p7037_1, p7057_2]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7024, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7030, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7033, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h1, h7030, h7036, hc01, hc45, hlam, hphi, ht0b, ht5b, p7057_1]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7025, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7031, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7034, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [h7036, hlam, p7057_0]
                                        · have p7057_0 := h7057c.1
                                          have p7057_1 := h7057c.2.1
                                          have p7057_2 := h7057c.2.2.1
                                          have p7057_3 := h7057c.2.2.2
                                          linarith only [hlam, p7057_0]
                                    · linarith only [h7035, h7054, hlam]
                                  · linarith only [h7034, h7053, hlam]
                                · linarith only [h7052, hlam, p7037_0]
                              · linarith only [h7023, h7051, hlam]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7037_1, u0ehi1]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              rcases p7037_3 (m.d 0 2) (by simp) with h7106 | h7106
                              · linarith only [h3, h7106, hlam]
                              · linarith only [h0, h7106, hlam]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h6383, h7023, hc23, hlam, hphi, ht01, ht12, p7037_1, u0ehi4]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              rcases p7037_3 (m.d 0 2) (by simp) with h7111 | h7111
                              · linarith only [h3, h7111, hlam]
                              · linarith only [h7023, h7111, hlam]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7023, hc24, hlam, hphi, ht01, ht12, p7037_1, u0ehi4]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              rcases p7037_3 (m.d 0 2) (by simp) with h7115 | h7115
                              · linarith only [h6383, h7115, hlam]
                              · linarith only [h0, h7115, hlam]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7033, hlam, p7037_1]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              rcases p7037_3 (m.d 0 2) (by simp) with h7120 | h7120
                              · linarith only [h6383, h7120, hlam]
                              · linarith only [h7023, h7120, hlam]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7023, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7029, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7034, hlam, p7037_1]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [h7035, hlam, p7037_0]
                            · have p7037_0 := h7037c.1
                              have p7037_1 := h7037c.2.1
                              have p7037_2 := h7037c.2.2.1
                              have p7037_3 := h7037c.2.2.2
                              linarith only [hlam, p7037_0]
                          · rcases h2bigk with h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c | h7128c
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7029, h7035, h7036, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h3, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h6383, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h6383, h7033, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h0, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7027, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h6383, hc12, hlam, hphi, ht01, p7128_1, u0ehi1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h0, h6383, h7035, h7036, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7128_1, u0ehi1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7029, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h0, h6383, h7029, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              rcases p7128_3 (m.d 0 2) (by simp) with h7143 | h7143
                              · linarith only [h3, h7143, hlam]
                              · linarith only [h7023, h7143, hlam]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h0, h7029, h7035, h7036, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7029, h7033, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7033, hlam, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              rcases p7128_3 (m.d 0 2) (by simp) with h7150 | h7150
                              · linarith only [h6383, h7150, hlam]
                              · linarith only [h7023, h7150, hlam]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7023, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7029, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7034, hlam, p7128_1]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [h7035, hlam, p7128_0]
                            · have p7128_0 := h7128c.1
                              have p7128_1 := h7128c.2.1
                              have p7128_2 := h7128c.2.2.1
                              have p7128_3 := h7128c.2.2.2
                              linarith only [hlam, p7128_0]
                        · linarith only [h6383, h7035, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h3, h7023, h7034, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h3, h7023, h7033, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7161 | h7161
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7162 | h7162
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7163 | h7163
                        · linarith only [h7029, h7032, h7163, hlam]
                        · linarith only [h6383, h7163, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h3, h7023, h7162, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h3, h7023, h7024, h7026, h7030, h7032, h7161, hc03, hlam, hphi, u0ehi4]
                · linarith only [h7027, h7029, h7031, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7169 | h7169
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7170 | h7170
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7171 | h7171
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7172 | h7172
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7173 | h7173
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7174 | h7174
                          · rcases h2bigk with h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c | h7175c
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p7175_1]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h3, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h6383, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              rcases p7175_3 (m.d 0 2) (by simp) with h7180 | h7180
                              · rcases p7175_3 (m.d 1 2) (by simp) with h7181 | h7181
                                · linarith only [h0, h7181, hlam]
                                · linarith only [h7029, h7181, hlam]
                              · linarith only [h7180, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h0, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7027, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h6383, hc12, hlam, hphi, ht01, p7175_1, u0ehi1]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h3, h7024, h7027, h7030, h7172, h7174, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7175_1]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7175_1, u0ehi1]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              rcases p7175_3 (m.d 0 2) (by simp) with h7191 | h7191
                              · linarith only [h3, h7191, hlam]
                              · linarith only [h0, h7191, hlam]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h6383, h7023, hc23, hlam, hphi, ht01, ht12, p7175_1, u0ehi4]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h3, h7024, h7027, h7029, h7030, hlam, p7175_2]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7023, hc24, hlam, hphi, ht01, ht12, p7175_1, u0ehi4]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              rcases p7175_3 (m.d 0 2) (by simp) with h7198 | h7198
                              · linarith only [h6383, h7198, hlam]
                              · linarith only [h0, h7198, hlam]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7171, hlam, p7175_1]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              rcases p7175_3 (m.d 0 2) (by simp) with h7203 | h7203
                              · linarith only [h6383, h7203, hlam]
                              · linarith only [h7023, h7203, hlam]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7023, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7029, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7172, hlam, p7175_1]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [h7173, hlam, p7175_0]
                            · have p7175_0 := h7175c.1
                              have p7175_1 := h7175c.2.1
                              have p7175_2 := h7175c.2.2.1
                              have p7175_3 := h7175c.2.2.2
                              linarith only [hlam, p7175_0]
                          · linarith only [h6383, h7026, h7027, h7030, h7174, hc12, hc24, hlam, hphi]
                        · linarith only [h6383, h7023, h7029, h7170, h7173, hc12, hlam, hphi, ht01, u0ehi4]
                      · linarith only [h3, h7024, h7027, h7030, h7172, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h3, h7024, h7171, hlam]
                  · linarith only [h7027, h7029, h7030, h7170, hlam]
                · linarith only [h7027, h7029, h7169, hlam]
            · linarith only [h3, h7023, h7029, hc12, hc23, hlam, hphi]
        · linarith only [h6383, h7023, h7026, hlam]
      · linarith only [h3, h7023, h7025, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7220 | h7220
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7221 | h7221
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7222 | h7222
          · linarith only [h3, h7222, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7224 | h7224
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7225 | h7225
              · linarith only [h1, h7024, h7225, hc01, hlam, hphi, u0ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7227 | h7227
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7228 | h7228
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7229 | h7229
                    · linarith only [h3, h7023, h7024, h7229, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                    · linarith only [h3, h7023, h7229, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · linarith only [h7222, h7224, h7225, h7228, hlam]
                · linarith only [h7024, h7220, h7222, h7224, h7227, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h3, h7023, h7024, h7224, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h3, h7023, h7024, h7221, hlam]
      · linarith only [h3, h7023, h7220, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7237 | h7237
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7238 | h7238
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7239 | h7239
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7240 | h7240
          · linarith only [h3, h7240, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7242 | h7242
            · linarith only [h7023, h7242, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7244 | h7244
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7245 | h7245
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7246 | h7246
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7247 | h7247
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7248 | h7248
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7249 | h7249
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7250 | h7250
                          · rcases h2bigk with h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c | h7251c
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7023, h7247, h7249, hc12, hc23, hlam, hphi, p7251_1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h3, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h6383, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7023, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h0, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7240, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7023, h7249, hc12, hlam, hphi, ht01, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7242, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              rcases p7251_3 (m.d 0 2) (by simp) with h7263 | h7263
                              · linarith only [h3, h7263, hlam]
                              · linarith only [h0, h7263, hlam]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7023, h7249, hc23, hlam, hphi, ht01, ht12, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7023, hc23, hlam, hphi, ht01, ht12, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              rcases p7251_3 (m.d 0 2) (by simp) with h7270 | h7270
                              · linarith only [h6383, h7270, hlam]
                              · linarith only [h0, h7270, hlam]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7247, hlam, p7251_1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7023, h7247, hc23, hlam, hphi, ht01, ht12, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p7251_1, u0ehi1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              rcases p7251_3 (m.d 0 2) (by simp) with h7277 | h7277
                              · linarith only [h7023, h7277, hlam]
                              · linarith only [h0, h7277, hlam]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7248, hlam, p7251_1]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [h7249, hlam, p7251_0]
                            · have p7251_0 := h7251c.1
                              have p7251_1 := h7251c.2.1
                              have p7251_2 := h7251c.2.2.1
                              have p7251_3 := h7251c.2.2.2
                              linarith only [hlam, p7251_0]
                          · rcases h2bigk with h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c | h7283c
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p7283_1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h3, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h6383, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7023, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h0, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7240, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7023, h7249, hc12, hlam, hphi, ht01, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7242, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              rcases p7283_3 (m.d 0 2) (by simp) with h7295 | h7295
                              · linarith only [h3, h7295, hlam]
                              · linarith only [h0, h7295, hlam]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7023, h7249, hc23, hlam, hphi, ht01, ht12, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7023, hc23, hlam, hphi, ht01, ht12, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              rcases p7283_3 (m.d 0 2) (by simp) with h7302 | h7302
                              · linarith only [h6383, h7302, hlam]
                              · linarith only [h0, h7302, hlam]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7247, hlam, p7283_1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7023, h7247, hc23, hlam, hphi, ht01, ht12, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p7283_1, u0ehi1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              rcases p7283_3 (m.d 0 2) (by simp) with h7309 | h7309
                              · linarith only [h7023, h7309, hlam]
                              · linarith only [h0, h7309, hlam]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7248, hlam, p7283_1]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [h7249, hlam, p7283_0]
                            · have p7283_0 := h7283c.1
                              have p7283_1 := h7283c.2.1
                              have p7283_2 := h7283c.2.2.1
                              have p7283_3 := h7283c.2.2.2
                              linarith only [hlam, p7283_0]
                        · linarith only [h6383, h7239, h7249, hc04, hlam, hphi, u0ehi1]
                      · linarith only [h1, h3, h7245, h7248, hc01, hlam, hphi, u0ehi1]
                    · linarith only [h3, h7247, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7318 | h7318
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7319 | h7319
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7320 | h7320
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7321 | h7321
                          · linarith only [h1, h7244, h7246, h7321, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h2bigk with h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c | h7323c
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p7323_1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h3, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h6383, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7023, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h0, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7240, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7023, h7242, h7320, hc15, hlam, hphi, ht01, p7323_1, u0ehi1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7242, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7323_1, u0ehi1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              rcases p7323_3 (m.d 0 2) (by simp) with h7335 | h7335
                              · linarith only [h3, h7335, hlam]
                              · linarith only [h0, h7335, hlam]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h6383, hc23, hlam, hphi, ht01, ht12, p7323_1, u0ehi3]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7023, hc23, hlam, hphi, ht01, ht12, p7323_1, u0ehi1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p7323_1, u0ehi1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              rcases p7323_3 (m.d 0 2) (by simp) with h7342 | h7342
                              · linarith only [h6383, h7342, hlam]
                              · linarith only [h0, h7342, hlam]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7318, hlam, p7323_1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7023, h7318, hc23, hlam, hphi, ht01, ht12, p7323_1, u0ehi1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p7323_1, u0ehi1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              rcases p7323_3 (m.d 0 2) (by simp) with h7349 | h7349
                              · linarith only [h7023, h7349, hlam]
                              · linarith only [h0, h7349, hlam]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7319, hlam, p7323_1]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [h7320, hlam, p7323_0]
                            · have p7323_0 := h7323c.1
                              have p7323_1 := h7323c.2.1
                              have p7323_2 := h7323c.2.2.1
                              have p7323_3 := h7323c.2.2.2
                              linarith only [hlam, p7323_0]
                        · linarith only [h6383, h7239, h7320, hc04, hlam, hphi, u0ehi1]
                      · linarith only [h1, h3, h7237, h7239, h7245, h7246, h7319, hc01, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3, h7237, h7239, h7244, h7246, h7318, hc03, hlam, hphi, u0ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7358 | h7358
                  · linarith only [h7244, h7245, h7358, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7360 | h7360
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7361 | h7361
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7362 | h7362
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7363 | h7363
                          · linarith only [h7244, h7245, h7358, h7363, hlam]
                          · rcases h2bigk with h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c | h7365c
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p7365_1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h3, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h6383, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7023, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h0, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7240, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7023, h7362, hc12, hlam, hphi, ht01, p7365_1, u0ehi1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7242, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7365_1, u0ehi1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              rcases p7365_3 (m.d 0 2) (by simp) with h7377 | h7377
                              · linarith only [h3, h7377, hlam]
                              · linarith only [h0, h7377, hlam]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h6383, h7239, h7240, h7245, h7363, hc12, hc23, hlam, hphi, p7365_1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7023, hc23, hlam, hphi, ht01, ht12, p7365_1, u0ehi1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p7365_1, u0ehi1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              rcases p7365_3 (m.d 0 2) (by simp) with h7384 | h7384
                              · linarith only [h6383, h7384, hlam]
                              · linarith only [h0, h7384, hlam]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7360, hlam, p7365_1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7023, h7360, hc23, hlam, hphi, ht01, ht12, p7365_1, u0ehi1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p7365_1, u0ehi1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              rcases p7365_3 (m.d 0 2) (by simp) with h7391 | h7391
                              · linarith only [h7023, h7391, hlam]
                              · linarith only [h0, h7391, hlam]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7361, hlam, p7365_1]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [h7362, hlam, p7365_0]
                            · have p7365_0 := h7365c.1
                              have p7365_1 := h7365c.2.1
                              have p7365_2 := h7365c.2.2.1
                              have p7365_3 := h7365c.2.2.2
                              linarith only [hlam, p7365_0]
                        · linarith only [h6383, h7237, h7239, h7362, hc03, hlam, hphi, u0ehi1]
                      · linarith only [h3, h7361, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h3, h7238, h7244, h7245, h7360, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7400 | h7400
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7401 | h7401
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7402 | h7402
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7403 | h7403
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7404 | h7404
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7405 | h7405
                          · rcases h2bigk with h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7023, h7404, hc12, hc24, hlam, hphi, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h3, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h6383, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7023, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h0, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7240, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7023, h7404, hc12, hlam, hphi, ht01, p7406_1, u0ehi1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7242, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7406_1, u0ehi1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              rcases p7406_3 (m.d 0 2) (by simp) with h7418 | h7418
                              · linarith only [h3, h7418, hlam]
                              · linarith only [h0, h7418, hlam]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h6383, hc23, hlam, hphi, ht01, ht12, p7406_1, u0ehi3]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7023, hc23, hlam, hphi, ht01, ht12, p7406_1, u0ehi1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p7406_1, u0ehi1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              rcases p7406_3 (m.d 0 2) (by simp) with h7425 | h7425
                              · linarith only [h6383, h7425, hlam]
                              · linarith only [h0, h7425, hlam]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7402, hlam, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7023, h7402, hc23, hlam, hphi, ht01, ht12, p7406_1, u0ehi1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p7406_1, u0ehi1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              rcases p7406_3 (m.d 0 2) (by simp) with h7432 | h7432
                              · linarith only [h7023, h7432, hlam]
                              · linarith only [h0, h7432, hlam]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7403, hlam, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7404, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                          · linarith only [h7239, h7244, h7400, h7405, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6383, h7404, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h7237, h7244, h7400, h7403, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3, h7237, h7402, hlam]
                  · linarith only [h7244, h7400, h7401, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7443 | h7443
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7444 | h7444
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7445 | h7445
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7446 | h7446
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7447 | h7447
                          · rcases h2bigk with h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c | h7448c
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p7448_1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h3, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h6383, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7023, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h0, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7240, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7023, h7446, hc12, hlam, hphi, ht01, p7448_1, u0ehi1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7242, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p7448_1, u0ehi1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              rcases p7448_3 (m.d 0 2) (by simp) with h7460 | h7460
                              · linarith only [h3, h7460, hlam]
                              · linarith only [h0, h7460, hlam]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h6383, hc23, hlam, hphi, ht01, ht12, p7448_1, u0ehi3]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7023, hc23, hlam, hphi, ht01, ht12, p7448_1, u0ehi1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p7448_1, u0ehi1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              rcases p7448_3 (m.d 0 2) (by simp) with h7467 | h7467
                              · linarith only [h6383, h7467, hlam]
                              · linarith only [h0, h7467, hlam]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7444, hlam, p7448_1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7023, h7444, hc23, hlam, hphi, ht01, ht12, p7448_1, u0ehi1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p7448_1, u0ehi1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              rcases p7448_3 (m.d 0 2) (by simp) with h7474 | h7474
                              · linarith only [h7023, h7474, hlam]
                              · linarith only [h0, h7474, hlam]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7445, hlam, p7448_1]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [h7446, hlam, p7448_0]
                            · have p7448_0 := h7448c.1
                              have p7448_1 := h7448c.2.1
                              have p7448_2 := h7448c.2.2.1
                              have p7448_3 := h7448c.2.2.2
                              linarith only [hlam, p7448_0]
                          · linarith only [h3, h7237, h7239, h7240, h7244, h7447, hc12, hc23, hlam, hphi]
                        · linarith only [h6383, h7237, h7244, h7443, h7446, hc03, hlam, hphi, u0ehi1]
                      · linarith only [h3, h7445, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h3, h7237, h7444, hc03, hlam, hphi, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7484 | h7484
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7485 | h7485
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7486 | h7486
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h7487 | h7487
                          · linarith only [h3, h7237, h7240, h7244, h7443, h7487, hc12, hc23, hlam, hphi]
                          · linarith only [h3, h7237, h7239, h7240, h7244, h7487, hc12, hc23, hlam, hphi]
                        · linarith only [h3, h6383, h7237, h7239, h7486, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h3, h7238, h7485, hlam]
                    · linarith only [h3, h7484, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7493 | h7493
          · linarith only [h3, h7493, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7495 | h7495
            · linarith only [h7023, h7495, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7497 | h7497
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7498 | h7498
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7499 | h7499
                  · linarith only [h7239, h7499, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7501 | h7501
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7502 | h7502
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7503 | h7503
                        · linarith only [h6383, h7239, h7501, h7503, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h6383, h7503, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h1, h3, h7498, h7502, hc03, hlam, hphi, u0ehi1]
                    · linarith only [h1, h3, h7497, h7501, hc01, hlam, hphi, u0ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7508 | h7508
                  · linarith only [h6383, h7238, h7239, h7497, h7498, h7508, hc03, hlam, hphi, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7510 | h7510
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7511 | h7511
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7512 | h7512
                        · linarith only [h6383, h7239, h7512, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h6383, h7512, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h3, h7238, h7511, hlam]
                    · linarith only [h3, h7238, h7497, h7498, h7510, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7517 | h7517
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7518 | h7518
                  · linarith only [h7237, h7239, h7497, h7517, h7518, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h7497, h7517, h7518, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7521 | h7521
                  · linarith only [h7239, h7521, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7523 | h7523
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7524 | h7524
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h7525 | h7525
                        · linarith only [h6383, h7239, h7525, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h6383, h7525, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h3, h7524, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h3, h7237, h7523, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7530 | h7530
        · linarith only [h7237, h7238, h7530, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7532 | h7532
          · linarith only [h3, h7532, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7534 | h7534
            · linarith only [h0, h7023, h7534, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7536 | h7536
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7537 | h7537
                · linarith only [h7238, h7537, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7539 | h7539
                  · linarith only [h6383, h7530, h7539, hc14, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7541 | h7541
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7542 | h7542
                      · linarith only [h6383, h7237, h7238, h7542, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h3, h7542, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h1, h3, h7536, h7541, hc03, hlam, hphi, u0ehi1]
              · linarith only [h7237, h7238, h7536, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7547 | h7547
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7548 | h7548
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7549 | h7549
          · linarith only [h0, h3, h7549, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7551 | h7551
            · linarith only [h7023, h7551, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7553 | h7553
              · linarith only [h1, h7237, h7553, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7555 | h7555
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7556 | h7556
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7557 | h7557
                    · linarith only [h7023, h7237, h7547, h7557, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3, h7557, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h7553, h7555, h7556, hlam]
                · linarith only [h7237, h7547, h7555, hc13, hc34, hlam, hphi]
        · linarith only [h7237, h7547, h7548, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7563 | h7563
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7564 | h7564
          · linarith only [h3, h7564, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7566 | h7566
            · linarith only [h0, h7023, h7566, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7568 | h7568
              · linarith only [h7237, h7568, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7570 | h7570
                · linarith only [h1, h7547, h7570, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7572 | h7572
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7573 | h7573
                    · linarith only [h3, h7237, h7573, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3, h7573, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7576 | h7576
                    · linarith only [h3, h7237, h7576, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3, h7576, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7579 | h7579
          · linarith only [h3, h7579, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7581 | h7581
            · linarith only [h0, h7023, h7581, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7583 | h7583
              · linarith only [h3, h7237, h7583, hc13, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7585 | h7585
                · linarith only [h1, h7547, h7585, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7587 | h7587
                  · linarith only [h7563, h7587, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7589 | h7589
                    · linarith only [h3, h7237, h7589, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3, h7589, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 15178000 in
set_option maxHeartbeats 15178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 4 (by decide) (by decide) with h6383 | h6383
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 h3 h6383
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 h3 h6383

set_option maxHeartbeats 15178000 in
set_option maxHeartbeats 15178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 h3
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 h3

set_option maxHeartbeats 15426000 in
set_option maxHeartbeats 15426000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7592 | h7592
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7593 | h7593
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7594 | h7594
        · linarith only [h0, h2, h7594, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7596 | h7596
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7597 | h7597
            · linarith only [h0, h2, h7592, h7597, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7599 | h7599
              · linarith only [h0, h2, h7592, h7596, h7599, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7601 | h7601
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7602 | h7602
                  · linarith only [h0, h2, h7593, h7594, h7602, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7604 | h7604
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7605 | h7605
                      · linarith only [h0, h2, h7596, h7597, h7601, h7602, h7605, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                      · linarith only [h0, h2, h7601, h7605, hc23, hc35, hlam, hphi]
                    · linarith only [h7596, h7597, h7604, hc13, hc35, hlam, hphi]
                · linarith only [h7592, h7594, h7601, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7610 | h7610
            · linarith only [h0, h2, h7593, h7596, h7610, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7612 | h7612
              · linarith only [h0, h2, h7593, h7612, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7614 | h7614
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7615 | h7615
                  · linarith only [h0, h2, h7594, h7615, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7617 | h7617
                    · linarith only [h7596, h7617, hc13, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7619 | h7619
                      · linarith only [h0, h2, h7610, h7614, h7615, h7619, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                      · linarith only [h0, h2, h7614, h7619, hc23, hc35, hlam, hphi]
                · linarith only [h7592, h7594, h7614, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7623 | h7623
        · linarith only [h0, h2, h7623, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7625 | h7625
          · linarith only [h7592, h7593, h7625, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7627 | h7627
            · linarith only [h0, h2, h7592, h7627, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7629 | h7629
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7630 | h7630
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7631 | h7631
                  · linarith only [h7623, h7631, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7633 | h7633
                    · linarith only [h7625, h7633, hc13, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7635 | h7635
                      · linarith only [h0, h2, h7627, h7630, h7631, h7635, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                      · linarith only [h0, h2, h7630, h7635, hc23, hc35, hlam, hphi]
                · linarith only [h7592, h7593, h7630, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7639 | h7639
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7640 | h7640
                  · linarith only [h0, h7592, h7623, h7640, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7642 | h7642
                    · linarith only [h7625, h7642, hc13, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7644 | h7644
                      · linarith only [h0, h2, h7627, h7639, h7640, h7644, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                      · linarith only [h0, h2, h7639, h7644, hc23, hc35, hlam, hphi]
                · linarith only [h7592, h7593, h7629, h7639, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7648 | h7648
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7649 | h7649
        · linarith only [h0, h2, h7649, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7651 | h7651
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7652 | h7652
            · linarith only [h1, h2, h7652, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7654 | h7654
              · linarith only [h1, h2, h7592, h7648, h7654, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7656 | h7656
                · linarith only [h7592, h7656, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7658 | h7658
                  · linarith only [h1, h2, h7649, h7656, h7658, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7660 | h7660
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7661 | h7661
                      · linarith only [h1, h2, h7592, h7648, h7652, h7658, h7661, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7663 | h7663
                        · linarith only [h1, h2, h7654, h7660, h7661, h7663, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1, h2, h7660, h7663, hc34, hc45, hlam, hphi]
                    · linarith only [h7651, h7652, h7656, h7660, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h7592, h7648, h7651, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7668 | h7668
        · linarith only [h0, h2, h7668, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7670 | h7670
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7671 | h7671
            · linarith only [h1, h2, h7671, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7673 | h7673
              · linarith only [h1, h2, h7670, h7673, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7675 | h7675
                · linarith only [h7592, h7675, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7677 | h7677
                  · linarith only [h1, h7668, h7675, h7677, hc01, hlam, hphi, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7679 | h7679
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7680 | h7680
                      · linarith only [h1, h2, h7648, h7670, h7671, h7677, h7680, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7682 | h7682
                        · linarith only [h1, h2, h7673, h7679, h7680, h7682, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                        · linarith only [h1, h2, h7679, h7682, hc34, hc45, hlam, hphi]
                    · linarith only [h7670, h7671, h7675, h7679, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7686 | h7686
            · linarith only [h1, h2, h7686, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7688 | h7688
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7689 | h7689
                · linarith only [h7592, h7689, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7691 | h7691
                  · linarith only [h7668, h7691, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7693 | h7693
                    · linarith only [h1, h2, h7670, h7691, h7693, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7695 | h7695
                      · linarith only [h1, h2, h7592, h7686, h7691, h7695, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7697 | h7697
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7698 | h7698
                          · linarith only [h1, h2, h7689, h7693, h7697, h7698, hc12, hc23, hlam, hphi]
                          · linarith only [h7592, h7698, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1, h2, h7592, h7688, h7697, hc04, hlam, hphi, u0ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7702 | h7702
                · linarith only [h7592, h7702, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7704 | h7704
                  · linarith only [h7668, h7704, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7706 | h7706
                    · linarith only [h1, h2, h7592, h7670, h7704, h7706, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7708 | h7708
                      · linarith only [h1, h2, h7592, h7686, h7704, h7708, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7710 | h7710
                        · linarith only [h7592, h7670, h7688, h7710, hc14, hlam, hphi, ht01, u0ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7712 | h7712
                          · linarith only [h7592, h7670, h7712, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h7592, h7712, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

end R2N4
