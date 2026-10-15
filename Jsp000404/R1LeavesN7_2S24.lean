import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14402 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h14861 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h15018 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 1 2 3 (by decide) (by decide) with h15019 | h15019
  · rcases m.htr 1 2 4 (by decide) (by decide) with h15020 | h15020
    · rcases m.htr 1 2 5 (by decide) (by decide) with h15021 | h15021
      · rcases m.htr 1 3 4 (by decide) (by decide) with h15022 | h15022
        · linarith only [h0, h14396, h14402, h15022, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15024 | h15024
          · linarith only [h14396, h14861, h15024, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15026 | h15026
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15027 | h15027
              · linarith only [h14396, h14402, h15019, h15027, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15029 | h15029
                · linarith only [h14396, h14861, h15019, h15029, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15031 | h15031
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15032 | h15032
                    · rcases h0bigk with h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c | h15033c
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h0, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15036 | h15036
                        · rcases p15033_3 (m.d 0 2) (by simp) with h15037 | h15037
                          · rcases p15033_3 (m.d 0 3) (by simp) with h15038 | h15038
                            · linarith only [h14396, h15038, hlam]
                            · rcases p15033_3 (m.d 0 4) (by simp) with h15040 | h15040
                              · linarith only [h14397, h15040, hlam]
                              · linarith only [h14402, h15040, hlam]
                          · linarith only [h14399, h15037, hlam]
                        · linarith only [h14396, h15036, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h0, h14397, h15020, h15031, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15046 | h15046
                        · rcases p15033_3 (m.d 0 2) (by simp) with h15047 | h15047
                          · rcases p15033_3 (m.d 0 3) (by simp) with h15048 | h15048
                            · linarith only [h14396, h15048, hlam]
                            · rcases p15033_3 (m.d 0 4) (by simp) with h15050 | h15050
                              · linarith only [h14397, h15050, hlam]
                              · linarith only [h15018, h15050, hlam]
                          · linarith only [h14401, h15047, hlam]
                        · linarith only [h14398, h15046, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h0, h14397, h15020, h15031, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15057 | h15057
                        · linarith only [h0, h15057, hlam]
                        · linarith only [h14396, h15057, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15060 | h15060
                        · linarith only [h0, h15060, hlam]
                        · linarith only [h14397, h15060, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15063 | h15063
                        · linarith only [h0, h15063, hlam]
                        · linarith only [h14398, h15063, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14396, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14399, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14402, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14861, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14397, hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14400, hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15073 | h15073
                        · rcases p15033_3 (m.d 0 2) (by simp) with h15074 | h15074
                          · rcases p15033_3 (m.d 0 3) (by simp) with h15075 | h15075
                            · linarith only [h14402, h15075, hlam]
                            · rcases p15033_3 (m.d 0 4) (by simp) with h15077 | h15077
                              · rcases p15033_3 (m.d 0 5) (by simp) with h15078 | h15078
                                · linarith only [h15018, h15078, hlam]
                                · linarith only [h14861, h15078, hlam]
                              · linarith only [h14402, h15077, hlam]
                          · linarith only [h14399, h15074, hlam]
                        · linarith only [h14396, h15073, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15085 | h15085
                        · rcases p15033_3 (m.d 0 2) (by simp) with h15086 | h15086
                          · rcases p15033_3 (m.d 0 3) (by simp) with h15087 | h15087
                            · linarith only [h14402, h15087, hlam]
                            · rcases p15033_3 (m.d 0 4) (by simp) with h15089 | h15089
                              · rcases p15033_3 (m.d 0 5) (by simp) with h15090 | h15090
                                · linarith only [h15018, h15090, hlam]
                                · rcases h2bigk with h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c | h15092c
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h0, hlam, p15092_1]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    rcases p15092_3 (m.d 0 2) (by simp) with h15095 | h15095
                                    · rcases p15092_3 (m.d 1 2) (by simp) with h15096 | h15096
                                      · rcases p15092_3 (m.d 2 3) (by simp) with h15097 | h15097
                                        · linarith only [h15097, hlam, p15092_0]
                                        · rcases p15092_3 (m.d 2 4) (by simp) with h15099 | h15099
                                          · linarith only [h14400, h15099, hlam]
                                          · linarith only [h15027, h15099, hlam]
                                      · linarith only [h15019, h15096, hlam]
                                    · linarith only [h15095, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    rcases p15092_3 (m.d 0 2) (by simp) with h15104 | h15104
                                    · rcases p15092_3 (m.d 1 2) (by simp) with h15105 | h15105
                                      · rcases p15092_3 (m.d 2 3) (by simp) with h15106 | h15106
                                        · linarith only [h14399, h15106, hlam]
                                        · rcases p15092_3 (m.d 2 4) (by simp) with h15108 | h15108
                                          · linarith only [h15108, hlam, p15092_0]
                                          · rcases p15092_3 (m.d 2 5) (by simp) with h15110 | h15110
                                            · linarith only [h14401, h15110, hlam]
                                            · rcases h3bigk with h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c | h15112c
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14397, h14861, h15019, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15033_1, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h0, h14397, h14861, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15033_1, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14402, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14861, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14396, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h0, h14396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15022, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15024, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14399, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15019, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15027, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15029, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15019, hc23, hc34, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14396, h14861, h15019, hc23, hc34, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h14396, h15019, hc23, hc35, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15019, hc23, hc35, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p15112_1]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [h15032, hlam, p15112_0]
                                              · have p15112_0 := h15112c.1
                                                have p15112_1 := h15112c.2.1
                                                have p15112_2 := h15112c.2.2.1
                                                have p15112_3 := h15112c.2.2.2
                                                linarith only [hlam, p15112_0]
                                      · linarith only [h15020, h15105, hlam]
                                    · linarith only [h15104, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    rcases p15092_3 (m.d 0 2) (by simp) with h15140 | h15140
                                    · rcases p15092_3 (m.d 1 2) (by simp) with h15141 | h15141
                                      · rcases p15092_3 (m.d 2 3) (by simp) with h15142 | h15142
                                        · linarith only [h14399, h15142, hlam]
                                        · rcases p15092_3 (m.d 2 4) (by simp) with h15144 | h15144
                                          · linarith only [h14400, h15144, hlam]
                                          · linarith only [h15031, h15144, hlam]
                                      · linarith only [h15021, h15141, hlam]
                                    · linarith only [h15140, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h0, h14397, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p15033_1, p15092_1]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h0, h14397, h14398, h15019, h15024, hlam, p15033_1, p15092_2]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    rcases p15092_3 (m.d 0 2) (by simp) with h15152 | h15152
                                    · linarith only [h0, h15152, hlam]
                                    · linarith only [h14400, h15152, hlam]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h0, h14397, h14401, hlam, p15033_1, p15092_2]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h14399, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h15019, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h15027, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h15029, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h14400, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h15020, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h0, h14397, h15020, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15092_1]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h0, h14397, h15020, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15092_1]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h14401, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h15021, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h14401, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15033_1, p15092_1]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [h15031, hlam, p15092_0]
                                  · have p15092_0 := h15092c.1
                                    have p15092_1 := h15092c.2.1
                                    have p15092_2 := h15092c.2.2.1
                                    have p15092_3 := h15092c.2.2.2
                                    linarith only [hlam, p15092_0]
                              · linarith only [h15018, h15089, hlam]
                          · linarith only [h14401, h15086, hlam]
                        · linarith only [h14398, h15085, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14398, hlam, p15033_0]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h14401, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        rcases p15033_3 (m.d 0 1) (by simp) with h15176 | h15176
                        · rcases p15033_3 (m.d 0 2) (by simp) with h15177 | h15177
                          · rcases p15033_3 (m.d 0 3) (by simp) with h15178 | h15178
                            · linarith only [h14861, h15178, hlam]
                            · rcases p15033_3 (m.d 0 4) (by simp) with h15180 | h15180
                              · rcases p15033_3 (m.d 0 5) (by simp) with h15181 | h15181
                                · rcases h2bigk with h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c | h15182c
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h0, hlam, p15182_1]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    rcases p15182_3 (m.d 0 2) (by simp) with h15185 | h15185
                                    · rcases p15182_3 (m.d 1 2) (by simp) with h15186 | h15186
                                      · rcases p15182_3 (m.d 2 3) (by simp) with h15187 | h15187
                                        · linarith only [h15187, hlam, p15182_0]
                                        · rcases p15182_3 (m.d 2 4) (by simp) with h15189 | h15189
                                          · linarith only [h14400, h15189, hlam]
                                          · linarith only [h15027, h15189, hlam]
                                      · linarith only [h15019, h15186, hlam]
                                    · linarith only [h15185, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    rcases p15182_3 (m.d 0 2) (by simp) with h15194 | h15194
                                    · rcases p15182_3 (m.d 1 2) (by simp) with h15195 | h15195
                                      · rcases p15182_3 (m.d 2 3) (by simp) with h15196 | h15196
                                        · linarith only [h14399, h15196, hlam]
                                        · rcases p15182_3 (m.d 2 4) (by simp) with h15198 | h15198
                                          · linarith only [h15198, hlam, p15182_0]
                                          · rcases p15182_3 (m.d 2 5) (by simp) with h15200 | h15200
                                            · linarith only [h14401, h15200, hlam]
                                            · rcases h3bigk with h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c | h15202c
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15019, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15033_1, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h0, h14398, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15033_1, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h14402, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h14861, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h14396, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h0, h14396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15022, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15024, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h14399, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15019, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15027, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15029, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15019, hc23, hc34, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h14396, h14861, h15019, hc23, hc34, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h14396, h15019, hc23, hc35, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15019, hc23, hc35, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p15202_1]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [h15032, hlam, p15202_0]
                                              · have p15202_0 := h15202c.1
                                                have p15202_1 := h15202c.2.1
                                                have p15202_2 := h15202c.2.2.1
                                                have p15202_3 := h15202c.2.2.2
                                                linarith only [hlam, p15202_0]
                                      · linarith only [h15020, h15195, hlam]
                                    · linarith only [h15194, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    rcases p15182_3 (m.d 0 2) (by simp) with h15230 | h15230
                                    · rcases p15182_3 (m.d 1 2) (by simp) with h15231 | h15231
                                      · rcases p15182_3 (m.d 2 3) (by simp) with h15232 | h15232
                                        · linarith only [h14399, h15232, hlam]
                                        · rcases p15182_3 (m.d 2 4) (by simp) with h15234 | h15234
                                          · linarith only [h14400, h15234, hlam]
                                          · linarith only [h15031, h15234, hlam]
                                      · linarith only [h15021, h15231, hlam]
                                    · linarith only [h15230, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h14400, h15031, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15182_1]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h0, h14396, h14397, h15018, h15019, hlam, p15033_1, p15182_2]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    rcases p15182_3 (m.d 0 2) (by simp) with h15242 | h15242
                                    · linarith only [h0, h15242, hlam]
                                    · linarith only [h14400, h15242, hlam]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    rcases p15182_3 (m.d 0 2) (by simp) with h15245 | h15245
                                    · linarith only [h0, h15245, hlam]
                                    · linarith only [h14401, h15245, hlam]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h14399, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h15019, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h15027, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h15029, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h14400, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h15020, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h0, h14397, h15020, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15182_1]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h0, h14397, h15020, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15182_1]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h14401, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h15021, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h0, h14397, h15021, h15026, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15182_1]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [h15031, hlam, p15182_0]
                                  · have p15182_0 := h15182c.1
                                    have p15182_1 := h15182c.2.1
                                    have p15182_2 := h15182c.2.2.1
                                    have p15182_3 := h15182c.2.2.2
                                    linarith only [hlam, p15182_0]
                                · linarith only [h14861, h15181, hlam]
                              · linarith only [h14402, h15180, hlam]
                          · linarith only [h14399, h15177, hlam]
                        · linarith only [h14396, h15176, hlam]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [h15018, hlam, p15033_1]
                      · have p15033_0 := h15033c.1
                        have p15033_1 := h15033c.2.1
                        have p15033_2 := h15033c.2.2.1
                        have p15033_3 := h15033c.2.2.2
                        linarith only [hlam, p15033_0]
                    · linarith only [h14402, h15018, h15032, hlam]
                  · linarith only [h0, h14397, h15026, h15031, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15271 | h15271
              · linarith only [h0, h14396, h14402, h15018, h15019, h15026, h15271, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15273 | h15273
                · linarith only [h0, h14397, h15018, h15019, h15022, h15026, h15273, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15275 | h15275
                  · linarith only [h15020, h15026, h15275, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15277 | h15277
                    · rcases h0bigk with h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c | h15278c
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h0, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        rcases p15278_3 (m.d 0 1) (by simp) with h15281 | h15281
                        · rcases p15278_3 (m.d 0 2) (by simp) with h15282 | h15282
                          · rcases p15278_3 (m.d 0 3) (by simp) with h15283 | h15283
                            · linarith only [h14396, h15283, hlam]
                            · rcases p15278_3 (m.d 0 4) (by simp) with h15285 | h15285
                              · linarith only [h14397, h15285, hlam]
                              · linarith only [h14402, h15285, hlam]
                          · linarith only [h14399, h15282, hlam]
                        · linarith only [h14396, h15281, hlam]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h0, h15018, h15019, h15022, h15026, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h0, h15018, h15019, h15022, h15026, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h0, h14397, h15018, h15019, h15022, h15026, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        rcases p15278_3 (m.d 0 1) (by simp) with h15294 | h15294
                        · linarith only [h0, h15294, hlam]
                        · linarith only [h14396, h15294, hlam]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h15018, h15019, h15022, h15026, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        rcases p15278_3 (m.d 0 1) (by simp) with h15298 | h15298
                        · linarith only [h0, h15298, hlam]
                        · linarith only [h14398, h15298, hlam]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14396, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14399, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14402, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14861, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14397, hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14400, hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        rcases p15278_3 (m.d 0 1) (by simp) with h15308 | h15308
                        · rcases p15278_3 (m.d 0 2) (by simp) with h15309 | h15309
                          · rcases p15278_3 (m.d 0 3) (by simp) with h15310 | h15310
                            · linarith only [h14402, h15310, hlam]
                            · rcases p15278_3 (m.d 0 4) (by simp) with h15312 | h15312
                              · rcases p15278_3 (m.d 0 5) (by simp) with h15313 | h15313
                                · linarith only [h15018, h15313, hlam]
                                · linarith only [h14861, h15313, hlam]
                              · linarith only [h14402, h15312, hlam]
                          · linarith only [h14399, h15309, hlam]
                        · linarith only [h14396, h15308, hlam]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14402, h15018, h15019, h15022, h15026, hc23, hc34, hlam, hphi, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14398, hlam, p15278_0]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h14401, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        rcases p15278_3 (m.d 0 1) (by simp) with h15323 | h15323
                        · rcases p15278_3 (m.d 0 2) (by simp) with h15324 | h15324
                          · rcases p15278_3 (m.d 0 3) (by simp) with h15325 | h15325
                            · linarith only [h14861, h15325, hlam]
                            · rcases p15278_3 (m.d 0 4) (by simp) with h15327 | h15327
                              · rcases p15278_3 (m.d 0 5) (by simp) with h15328 | h15328
                                · rcases h2bigk with h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c | h15329c
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h0, hlam, p15329_1]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    rcases p15329_3 (m.d 0 2) (by simp) with h15332 | h15332
                                    · rcases p15329_3 (m.d 1 2) (by simp) with h15333 | h15333
                                      · rcases p15329_3 (m.d 2 3) (by simp) with h15334 | h15334
                                        · linarith only [h15334, hlam, p15329_0]
                                        · rcases p15329_3 (m.d 2 4) (by simp) with h15336 | h15336
                                          · linarith only [h14400, h15336, hlam]
                                          · linarith only [h15271, h15336, hlam]
                                      · linarith only [h15019, h15333, hlam]
                                    · linarith only [h15332, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    rcases p15329_3 (m.d 0 2) (by simp) with h15341 | h15341
                                    · rcases p15329_3 (m.d 1 2) (by simp) with h15342 | h15342
                                      · rcases p15329_3 (m.d 2 3) (by simp) with h15343 | h15343
                                        · linarith only [h14399, h15343, hlam]
                                        · rcases p15329_3 (m.d 2 4) (by simp) with h15345 | h15345
                                          · linarith only [h15345, hlam, p15329_0]
                                          · rcases p15329_3 (m.d 2 5) (by simp) with h15347 | h15347
                                            · linarith only [h14401, h15347, hlam]
                                            · linarith only [h15275, h15347, hlam]
                                      · linarith only [h15020, h15342, hlam]
                                    · linarith only [h15341, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    rcases p15329_3 (m.d 0 2) (by simp) with h15352 | h15352
                                    · rcases p15329_3 (m.d 1 2) (by simp) with h15353 | h15353
                                      · rcases p15329_3 (m.d 2 3) (by simp) with h15354 | h15354
                                        · linarith only [h14399, h15354, hlam]
                                        · rcases p15329_3 (m.d 2 4) (by simp) with h15356 | h15356
                                          · linarith only [h14400, h15356, hlam]
                                          · rcases p15329_3 (m.d 2 5) (by simp) with h15358 | h15358
                                            · linarith only [h15358, hlam, p15329_0]
                                            · rcases h3bigk with h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c | h15360c
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15019, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15278_1, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h0, h14398, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15278_1, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h14402, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h14861, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h14396, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15022, h15026, hc23, hc45, hlam, hphi, ht34, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15022, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15024, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h14399, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15019, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15271, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15273, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15019, hc23, hc34, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h14396, h14861, h15019, hc23, hc34, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h14396, h15019, hc23, hc35, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15019, hc23, hc35, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p15360_1]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [h15277, hlam, p15360_0]
                                              · have p15360_0 := h15360c.1
                                                have p15360_1 := h15360c.2.1
                                                have p15360_2 := h15360c.2.2.1
                                                have p15360_3 := h15360c.2.2.2
                                                linarith only [hlam, p15360_0]
                                      · linarith only [h15021, h15353, hlam]
                                    · linarith only [h15352, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h0, h14397, h15018, h15026, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15329_1]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h0, h14396, h14397, h15018, h15019, hlam, p15278_1, p15329_2]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h0, h14397, h15018, h15020, h15026, hlam, p15329_2]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    rcases p15329_3 (m.d 0 2) (by simp) with h15392 | h15392
                                    · linarith only [h0, h15392, hlam]
                                    · linarith only [h14401, h15392, hlam]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h14399, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h15019, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h15271, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h15273, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h14400, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h15020, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h14397, h15018, h15020, h15026, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15329_1]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h15275, hlam, p15329_1]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h14401, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h15021, hlam, p15329_0]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h0, h14397, h15018, h15021, h15026, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15329_1]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [h0, h14397, h15018, h15021, h15026, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15329_1]
                                  · have p15329_0 := h15329c.1
                                    have p15329_1 := h15329c.2.1
                                    have p15329_2 := h15329c.2.2.1
                                    have p15329_3 := h15329c.2.2.2
                                    linarith only [hlam, p15329_0]
                                · linarith only [h14861, h15328, hlam]
                              · linarith only [h14402, h15327, hlam]
                          · linarith only [h14399, h15324, hlam]
                        · linarith only [h14396, h15323, hlam]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [h15018, hlam, p15278_1]
                      · have p15278_0 := h15278c.1
                        have p15278_1 := h15278c.2.1
                        have p15278_2 := h15278c.2.2.1
                        have p15278_3 := h15278c.2.2.2
                        linarith only [hlam, p15278_0]
                    · linarith only [h0, h14396, h14397, h14402, h15018, h15019, h15277, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h14397, h14401, h15018, h15021, hc02, hc45, hlam, hphi, ht0b, ht5b]
    · linarith only [h0, h14400, h15020, hlam]
  · linarith only [h0, h14399, h15019, hlam]

end R2N4
