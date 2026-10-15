import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4215 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 0 4 5 (by decide) (by decide) with h4216 | h4216
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4217 | h4217
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4218 | h4218
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4219 | h4219
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4220 | h4220
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4221 | h4221
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4222 | h4222
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4223 | h4223
                · linarith only [h1965, h1967, h1968, h4215, h4223, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4225 | h4225
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4226 | h4226
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4227 | h4227
                      · rcases h0bigk with h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c | h4228c
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h0, hlam, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1414, hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1728, h1967, h1968, h4215, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4228_1, u2ehi4]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1728, hlam, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          rcases p4228_3 (m.d 0 1) (by simp) with h4234 | h4234
                          · linarith only [h0, h4234, hlam]
                          · rcases p4228_3 (m.d 0 2) (by simp) with h4236 | h4236
                            · rcases p4228_3 (m.d 0 3) (by simp) with h4237 | h4237
                              · linarith only [h1965, h4237, hlam]
                              · linarith only [h1414, h4237, hlam]
                            · linarith only [h0, h4236, hlam]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          rcases p4228_3 (m.d 0 1) (by simp) with h4242 | h4242
                          · linarith only [h0, h4242, hlam]
                          · rcases p4228_3 (m.d 0 2) (by simp) with h4244 | h4244
                            · rcases p4228_3 (m.d 0 3) (by simp) with h4245 | h4245
                              · linarith only [h1965, h4245, hlam]
                              · rcases p4228_3 (m.d 0 4) (by simp) with h4247 | h4247
                                · linarith only [h1966, h4247, hlam]
                                · linarith only [h1968, h4247, hlam]
                            · linarith only [h1965, h4244, hlam]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          rcases p4228_3 (m.d 0 1) (by simp) with h4251 | h4251
                          · linarith only [h0, h4251, hlam]
                          · rcases p4228_3 (m.d 0 2) (by simp) with h4253 | h4253
                            · rcases p4228_3 (m.d 0 3) (by simp) with h4254 | h4254
                              · linarith only [h1965, h4254, hlam]
                              · rcases p4228_3 (m.d 0 4) (by simp) with h4256 | h4256
                                · linarith only [h1966, h4256, hlam]
                                · rcases p4228_3 (m.d 0 5) (by simp) with h4258 | h4258
                                  · linarith only [h1967, h4258, hlam]
                                  · rcases h0emax with h4260 | h4260 | h4260 | h4260 | h4260
                                    · rcases h5bigk with h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h1728, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4215, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4261_1, u2ehi4]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h1728, h4220, h4222, hc01, hc13, hlam, hphi, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4217, h4220, h4222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4261_1, u2ehi4]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        rcases p4261_3 (m.d 0 5) (by simp) with h4270 | h4270
                                        · linarith only [h1728, h4270, hlam]
                                        · linarith only [h4215, h4270, hlam]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        rcases p4261_3 (m.d 0 5) (by simp) with h4273 | h4273
                                        · linarith only [h1728, h4273, hlam]
                                        · linarith only [h4216, h4273, hlam]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h1967, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4219, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h1967, h4227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h1967, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4215, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4221, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4225, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4216, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4222, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4226, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4227, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                    · linarith only [h1968, h4260, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p4228_1]
                                    · rcases h5bigk with h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h1728, hlam, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h1968, h4215, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4228_1, p4292_1, u2ehi4]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h1728, h4217, h4220, h4222, hc01, hc12, hlam, hphi, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4217, h4220, h4222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4292_1, u2ehi4]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        rcases p4292_3 (m.d 0 5) (by simp) with h4301 | h4301
                                        · linarith only [h1728, h4301, hlam]
                                        · linarith only [h4215, h4301, hlam]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        rcases p4292_3 (m.d 0 5) (by simp) with h4304 | h4304
                                        · linarith only [h1728, h4304, hlam]
                                        · linarith only [h4216, h4304, hlam]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h1967, hlam, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4219, hlam, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h1967, h4227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h1967, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4215, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4221, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4225, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4216, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4222, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4226, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4227, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                    · rcases h5bigk with h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h1728, hlam, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h1728, h4217, h4220, h4222, hc01, hc12, hlam, hphi, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4217, h4220, h4222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4322_1, u2ehi4]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        rcases p4322_3 (m.d 0 5) (by simp) with h4331 | h4331
                                        · linarith only [h1728, h4331, hlam]
                                        · linarith only [h4215, h4331, hlam]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        rcases p4322_3 (m.d 0 5) (by simp) with h4334 | h4334
                                        · linarith only [h1728, h4334, hlam]
                                        · linarith only [h4216, h4334, hlam]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h1967, hlam, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4219, hlam, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h0, h1967, h4227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h0, h1967, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4215, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4221, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4225, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4322_1]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4216, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4222, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4226, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [h4227, hlam, p4322_0]
                                      · have p4322_0 := h4322c.1
                                        have p4322_1 := h4322c.2.1
                                        have p4322_2 := h4322c.2.2.1
                                        have p4322_3 := h4322c.2.2.2
                                        linarith only [hlam, p4322_0]
                                    · rcases h5bigk with h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c | h4352c
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h1728, hlam, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h1728, h4217, h4220, h4222, hc01, hc12, hlam, hphi, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4217, h4220, h4222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4352_1, u2ehi4]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        rcases p4352_3 (m.d 0 5) (by simp) with h4361 | h4361
                                        · linarith only [h1728, h4361, hlam]
                                        · linarith only [h4215, h4361, hlam]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        rcases p4352_3 (m.d 0 5) (by simp) with h4364 | h4364
                                        · linarith only [h1728, h4364, hlam]
                                        · linarith only [h4216, h4364, hlam]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h1967, hlam, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4219, hlam, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h0, h1967, h4227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h0, h1967, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4215, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4221, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4225, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4228_1, p4352_1]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4216, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4222, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4226, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [h4227, hlam, p4352_0]
                                      · have p4352_0 := h4352c.1
                                        have p4352_1 := h4352c.2.1
                                        have p4352_2 := h4352c.2.2.1
                                        have p4352_3 := h4352c.2.2.2
                                        linarith only [hlam, p4352_0]
                            · linarith only [h1966, h4253, hlam]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          rcases p4228_3 (m.d 0 1) (by simp) with h4383 | h4383
                          · linarith only [h0, h4383, hlam]
                          · rcases p4228_3 (m.d 0 2) (by simp) with h4385 | h4385
                            · rcases p4228_3 (m.d 0 3) (by simp) with h4386 | h4386
                              · linarith only [h1965, h4386, hlam]
                              · linarith only [h4215, h4386, hlam]
                            · linarith only [h1967, h4385, hlam]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1968, h4217, h4220, hc01, hc12, hlam, hphi, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1965, hlam, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1968, hlam, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1967, h1968, h4217, h4220, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4228_1, u2ehi4]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1968, h4217, h4220, hc01, hc12, hlam, hphi, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1966, hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1965, h1968, h4217, h4220, h4225, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1967, h1968, h4217, h4220, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4228_1, u2ehi4]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1968, h4215, h4217, h4220, hc01, hc12, hlam, hphi, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h1967, hlam, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h4215, hlam, p4228_0]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [h4216, hlam, p4228_1]
                        · have p4228_0 := h4228c.1
                          have p4228_1 := h4228c.2.1
                          have p4228_2 := h4228c.2.2.1
                          have p4228_3 := h4228c.2.2.2
                          linarith only [hlam, p4228_0]
                      · linarith only [h1965, h1968, h4225, h4227, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h1968, h4215, h4216, h4217, h4220, h4226, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h1968, h4215, h4217, h4220, h4225, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h1968, h4215, h4216, h4217, h4218, h4220, h4222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h1968, h4215, h4220, h4221, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4410 | h4410
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4411 | h4411
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4412 | h4412
                · linarith only [h1414, h1965, h4220, h4412, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4414 | h4414
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4415 | h4415
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4416 | h4416
                      · rcases h0bigk with h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h0, hlam, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1414, hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1728, h1966, h4410, h4412, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4417_1, u2ehi2]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1728, hlam, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          rcases p4417_3 (m.d 0 1) (by simp) with h4423 | h4423
                          · linarith only [h0, h4423, hlam]
                          · rcases p4417_3 (m.d 0 2) (by simp) with h4425 | h4425
                            · rcases p4417_3 (m.d 0 3) (by simp) with h4426 | h4426
                              · linarith only [h1965, h4426, hlam]
                              · linarith only [h1414, h4426, hlam]
                            · linarith only [h0, h4425, hlam]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          rcases p4417_3 (m.d 0 1) (by simp) with h4431 | h4431
                          · linarith only [h0, h4431, hlam]
                          · rcases p4417_3 (m.d 0 2) (by simp) with h4433 | h4433
                            · rcases p4417_3 (m.d 0 3) (by simp) with h4434 | h4434
                              · linarith only [h1965, h4434, hlam]
                              · rcases p4417_3 (m.d 0 4) (by simp) with h4436 | h4436
                                · linarith only [h1966, h4436, hlam]
                                · linarith only [h1968, h4436, hlam]
                            · linarith only [h1965, h4433, hlam]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          rcases p4417_3 (m.d 0 1) (by simp) with h4440 | h4440
                          · linarith only [h0, h4440, hlam]
                          · rcases p4417_3 (m.d 0 2) (by simp) with h4442 | h4442
                            · rcases p4417_3 (m.d 0 3) (by simp) with h4443 | h4443
                              · linarith only [h1965, h4443, hlam]
                              · rcases p4417_3 (m.d 0 4) (by simp) with h4445 | h4445
                                · linarith only [h1966, h4445, hlam]
                                · rcases p4417_3 (m.d 0 5) (by simp) with h4447 | h4447
                                  · linarith only [h1967, h4447, hlam]
                                  · rcases h0emax with h4449 | h4449 | h4449 | h4449 | h4449
                                    · rcases h5bigk with h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c | h4450c
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h1728, hlam, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4215, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4450_1, u2ehi4]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1968, h4215, h4416, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4220, h4410, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4220, h4410, hc34, hlam, hphi, ht23, p4450_1, u2ehi4]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, h4416, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4450_1, u2ehi4]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4450_1, u2ehi4]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h1967, hlam, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4219, hlam, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, h4416, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4215, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4410, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4414, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4450_1]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4216, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4411, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4415, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [h4416, hlam, p4450_0]
                                      · have p4450_0 := h4450c.1
                                        have p4450_1 := h4450c.2.1
                                        have p4450_2 := h4450c.2.2.1
                                        have p4450_3 := h4450c.2.2.2
                                        linarith only [hlam, p4450_0]
                                    · linarith only [h1965, h1968, h4414, h4449, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4417_1, u2ehi4]
                                    · rcases h5bigk with h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h1728, hlam, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4477_1, u2ehi4]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc05, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4477_1, u2ehi4]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4220, h4410, hc34, hlam, hphi, ht23, p4477_1, u2ehi4]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc35, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4477_1, u2ehi4]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4477_1, u2ehi4]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h1967, hlam, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4219, hlam, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4215, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4410, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4414, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4477_1]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4216, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4411, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4415, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [h4416, hlam, p4477_0]
                                      · have p4477_0 := h4477c.1
                                        have p4477_1 := h4477c.2.1
                                        have p4477_2 := h4477c.2.2.1
                                        have p4477_3 := h4477c.2.2.2
                                        linarith only [hlam, p4477_0]
                                    · rcases h5bigk with h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c | h4503c
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h1728, hlam, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4503_1, u2ehi4]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc05, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4503_1, u2ehi4]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4220, h4410, hc34, hlam, hphi, ht23, p4503_1, u2ehi4]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc35, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4503_1, u2ehi4]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4503_1, u2ehi4]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h1967, hlam, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4219, hlam, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4215, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4410, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4414, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4503_1]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4216, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4411, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4415, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [h4416, hlam, p4503_0]
                                      · have p4503_0 := h4503c.1
                                        have p4503_1 := h4503c.2.1
                                        have p4503_2 := h4503c.2.2.1
                                        have p4503_3 := h4503c.2.2.2
                                        linarith only [hlam, p4503_0]
                                    · rcases h5bigk with h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h1728, hlam, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4529_1, u2ehi4]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc05, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4529_1, u2ehi4]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4220, h4410, hc34, hlam, hphi, ht23, p4529_1, u2ehi4]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc35, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4529_1, u2ehi4]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1965, h1968, h4220, h4410, h4414, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4417_1, p4529_1, u2ehi4]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h1967, hlam, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4219, hlam, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1965, h1968, h4414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4215, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4410, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4414, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h0, h1968, h4215, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4417_1, p4529_1]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4216, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4411, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4415, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [h4416, hlam, p4529_0]
                                      · have p4529_0 := h4529c.1
                                        have p4529_1 := h4529c.2.1
                                        have p4529_2 := h4529c.2.2.1
                                        have p4529_3 := h4529c.2.2.2
                                        linarith only [hlam, p4529_0]
                            · linarith only [h1966, h4442, hlam]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          rcases p4417_3 (m.d 0 1) (by simp) with h4556 | h4556
                          · linarith only [h0, h4556, hlam]
                          · rcases p4417_3 (m.d 0 2) (by simp) with h4558 | h4558
                            · rcases p4417_3 (m.d 0 3) (by simp) with h4559 | h4559
                              · linarith only [h1965, h4559, hlam]
                              · linarith only [h4215, h4559, hlam]
                            · linarith only [h1967, h4558, hlam]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1414, h4220, hc01, hc34, hlam, hphi, ht12, ht23, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1965, hlam, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1968, hlam, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1414, h1967, h4220, hc34, hlam, hphi, ht23, p4417_1, u2ehi4]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          rcases p4417_3 (m.d 0 1) (by simp) with h4568 | h4568
                          · linarith only [h4568, hlam, p4417_0]
                          · rcases p4417_3 (m.d 0 2) (by simp) with h4570 | h4570
                            · rcases p4417_3 (m.d 0 3) (by simp) with h4571 | h4571
                              · linarith only [h1968, h4571, hlam]
                              · linarith only [h1414, h4571, hlam]
                            · linarith only [h0, h4570, hlam]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1966, hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1965, h1968, hc34, hlam, hphi, ht23, p4417_1, u2ehi2]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1967, h1968, hc34, hlam, hphi, ht23, p4417_1, u2ehi4]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1968, h4215, hc01, hc34, hlam, hphi, ht12, ht23, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h1967, hlam, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h4215, hlam, p4417_0]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [h4216, hlam, p4417_1]
                        · have p4417_0 := h4417c.1
                          have p4417_1 := h4417c.2.1
                          have p4417_2 := h4417c.2.2.1
                          have p4417_3 := h4417c.2.2.2
                          linarith only [hlam, p4417_0]
                      · linarith only [h1414, h4220, h4416, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1728, h4216, h4220, h4410, h4412, h4414, h4415, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h1414, h4215, h4220, h4414, hc34, hlam, hphi, ht23, u2ehi2]
              · linarith only [h1728, h4216, h4218, h4220, h4410, h4411, hc34, hlam, hphi, ht23, u2ehi3]
            · linarith only [h1414, h4215, h4410, hlam]
        · linarith only [h0, h1965, h4219, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1965, h4218, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1965, h4217, hlam]
  · linarith only [h1968, h4215, h4216, hlam]

end R2N4
